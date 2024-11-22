/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import polyglot.ast.Call;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.contains(method)) return;
        callGraph.addReachableMethod(method);
        method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            var pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet diff = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof VarPtr varPtr) {
                Var variable = varPtr.getVar();
                for (var obj : diff) {
                    variable.getStoreFields().forEach(stmt -> {
                        assert !stmt.isStatic();
                        Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
                        Pointer target = pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve());
                        addPFGEdge(source, target);
                    });
                    variable.getLoadFields().forEach(stmt -> {
                        assert !stmt.isStatic();
                        Pointer source = pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve());
                        Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
                        addPFGEdge(source, target);
                    });
                    variable.getStoreArrays().forEach(stmt -> {
                        Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
                        Pointer target = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    });
                    variable.getLoadArrays().forEach(stmt -> {
                        Pointer source = pointerFlowGraph.getArrayIndex(obj);
                        Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
                        addPFGEdge(source, target);
                    });
                    processCall(variable, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diff = new PointsToSet();
        pointsToSet.forEach(obj -> {
            if (!pointer.getPointsToSet().contains(obj)) {
                diff.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
            }
        });
        if (!diff.isEmpty()) {
            for (var succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, diff);
            }
        }
        return diff;
    }

    private void invokeMethod(Invoke stmt, JMethod method) {
        List<Var> args = stmt.getInvokeExp().getArgs();
        List<Var> params = method.getIR().getParams();
        assert args.size() == params.size();
        for (int i = 0; i < args.size(); i++) {
            Pointer source = pointerFlowGraph.getVarPtr(args.get(i));
            Pointer target = pointerFlowGraph.getVarPtr(params.get(i));
            addPFGEdge(source, target);
        }
        if (stmt.getResult() != null) {
            List<Var> rets = method.getIR().getReturnVars();
            Pointer target = pointerFlowGraph.getVarPtr(stmt.getResult());
            for (Var ret : rets) {
                Pointer source = pointerFlowGraph.getVarPtr(ret);
                addPFGEdge(source, target);
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        var.getInvokes().forEach(stmt -> {
            JMethod method = resolveCallee(recv, stmt);
            Pointer mthis = pointerFlowGraph.getVarPtr(method.getIR().getThis());
            workList.addEntry(mthis, new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, method))) {
                addReachable(method);
                invokeMethod(stmt, method);
            }
        });
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            PointsToSet pts = new PointsToSet(heapModel.getObj(stmt));
            Pointer pointer = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(pointer, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
            Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Pointer source = pointerFlowGraph.getStaticField(field);
                Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Pointer target = pointerFlowGraph.getStaticField(field);
                Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = stmt.getMethodRef().resolve();
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, method))) {
                    addReachable(method);
                    invokeMethod(stmt, method);
                }
            }
            return null;
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
