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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.contains(csMethod)) return;
        callGraph.addReachableMethod(csMethod);
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        csMethod.getMethod().getIR().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(heapContext, obj);

            PointsToSet pts = PointsToSetFactory.make(csObj);
            Pointer pointer = csManager.getCSVar(context, stmt.getLValue());
            workList.addEntry(pointer, pts);

            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer source = csManager.getCSVar(context, stmt.getRValue());
            Pointer target = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Pointer source = csManager.getStaticField(field);
                Pointer target = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Pointer source = csManager.getCSVar(context,stmt.getRValue());
                Pointer target = csManager.getStaticField(field);
                addPFGEdge(source, target);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);

                JMethod targetMethod = stmt.getMethodRef().resolve();
                Context methodContext = contextSelector.selectContext(csCallSite, targetMethod);
                CSMethod csTargetMethod = csManager.getCSMethod(methodContext, targetMethod);

                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, csTargetMethod))) {
                    addReachable(csTargetMethod);
                    invokeMethod(csCallSite, csTargetMethod);
                }
            }
            return null;
        }
    }

    private void invokeMethod(CSCallSite csCallSite, CSMethod csMethod) {
        Context callContext = csCallSite.getContext();
        Context methodContext = csMethod.getContext();

        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
        List<Var> params = csMethod.getMethod().getIR().getParams();
        assert args.size() == params.size();
        for (int i = 0; i < args.size(); i++) {
            Pointer source = csManager.getCSVar(callContext, args.get(i));
            Pointer target = csManager.getCSVar(methodContext, params.get(i));
            addPFGEdge(source, target);
        }

        Var callResult = csCallSite.getCallSite().getResult();
        if (callResult != null) {
            List<Var> rets = csMethod.getMethod().getIR().getReturnVars();
            Pointer target = csManager.getCSVar(callContext, callResult);
            for (Var ret : rets) {
                Pointer source = csManager.getCSVar(methodContext, ret);
                addPFGEdge(source, target);
            }
        }
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
            if (diff.isEmpty())
                continue;
            if (entry.pointer() instanceof CSVar csVar) {
                Var variable = csVar.getVar();
                Context varContext = csVar.getContext();
                for (var csObj : diff) {
                    variable.getStoreFields().forEach(stmt -> {
                        Pointer source = csManager.getCSVar(varContext, stmt.getRValue());
                        Pointer target = csManager.getInstanceField(csObj,stmt.getFieldRef().resolve());
                        addPFGEdge(source, target);
                    });
                    variable.getLoadFields().forEach(stmt -> {
                        Pointer source = csManager.getInstanceField(csObj, stmt.getFieldRef().resolve());
                        Pointer target = csManager.getCSVar(varContext, stmt.getLValue());
                        addPFGEdge(source, target);
                    });
                    variable.getStoreArrays().forEach(stmt -> {
                        Pointer source = csManager.getCSVar(varContext, stmt.getRValue());
                        Pointer target = csManager.getArrayIndex(csObj);
                        addPFGEdge(source, target);
                    });
                    variable.getLoadArrays().forEach(stmt -> {
                        Pointer source = csManager.getArrayIndex(csObj);
                        Pointer target = csManager.getCSVar(varContext, stmt.getLValue());
                        addPFGEdge(source, target);
                    });
                    processCall(csVar, csObj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diff = PointsToSetFactory.make();
        pointsToSet.forEach(obj -> {
            if (!pointer.getPointsToSet().contains(obj)) {
                diff.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
            }
        });
        if (!diff.isEmpty()) {
            for (var succ : pointerFlowGraph.getSuccsOf(pointer))
                workList.addEntry(succ, diff);
        }
        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param csVar    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar csVar, CSObj recvObj) {
        Context callContext = csVar.getContext();
        csVar.getVar().getInvokes().forEach(stmt -> {
            CSCallSite csCallSite = csManager.getCSCallSite(callContext, stmt);

            JMethod targetMethod = resolveCallee(recvObj, stmt);
            Context methodContext = contextSelector.selectContext(csCallSite, recvObj, targetMethod);
            CSMethod csTargetMethod = csManager.getCSMethod(methodContext, targetMethod);

            Pointer mthis = csManager.getCSVar(methodContext, targetMethod.getIR().getThis());
            workList.addEntry(mthis, PointsToSetFactory.make(recvObj));

            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, csTargetMethod))) {
                addReachable(csTargetMethod);
                invokeMethod(csCallSite, csTargetMethod);
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
