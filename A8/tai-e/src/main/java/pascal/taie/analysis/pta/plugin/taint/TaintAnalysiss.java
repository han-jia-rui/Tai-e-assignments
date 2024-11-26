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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final Set<TaintFlow> taintFlows;

    record ContextEdge(Pointer target, Type type) {}

    private final MultiMap<Pointer, ContextEdge> contextFlowMap = Maps.newMultiMap();

    record CallSiteIndex(Invoke callSite, int index) {}

    private final MultiMap<CallSiteIndex, CSVar> sinkMap = Maps.newMultiMap();

    public void addCFGEdge(Pointer source, Pointer target, Type type) {
        if (contextFlowMap.put(source, new ContextEdge(target, type))) {
            PointsToSet taintPts = getTaintPts(source.getPointsToSet(), type);
            if (! taintPts.isEmpty()){
                solver.addEntry(target, taintPts);
            }
        }
    }

    public void propagateTaint(Pointer pointer, PointsToSet pointsToSet) {
        contextFlowMap.get(pointer).forEach(edge -> {
            PointsToSet taintPts = getTaintPts(pointsToSet, edge.type());
            if (! taintPts.isEmpty()){
                solver.addEntry(edge.target, taintPts);
            }
        });
    }


    public PointsToSet getTaintPts(PointsToSet pts, Type type) {
        PointsToSet taintPts = PointsToSetFactory.make();
        pts.forEach(csobj -> {
            Obj obj = csobj.getObject();
            if (manager.isTaint(obj)) {
                taintPts.addObject(makeTaint(manager.getSourceCall(obj), type));
            }
        });
        return taintPts;
    }

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
        taintFlows = new TreeSet<>();
    }

    private CSObj makeTaint(Invoke callSite, Type type) {
        return solver.getCSManager().getCSObj(
                solver.getContextSelector().getEmptyContext(),
                manager.makeTaint(callSite, type)
        );
    }

    public PointsToSet checkSource(Invoke callSite) {
        JMethod method = callSite.getMethodRef().resolve();
        Type type = callSite.getMethodRef().getReturnType();

        PointsToSet taintPts = PointsToSetFactory.make();
        Source source = new Source(method, type);
        if (config.getSources().contains(source)) {
            taintPts.addObject(makeTaint(callSite, type));
        }
        return taintPts;
    }

    public void checkBaseToResult(Invoke callSite, Pointer base, Pointer target) {
        JMethod method = callSite.getMethodRef().resolve();
        for (var transfer : config.getTransfers()) {
            if (transfer.method().equals(method) && transfer.from() == TaintTransfer.BASE && transfer.to() == TaintTransfer.RESULT) {
                addCFGEdge(base, target, transfer.type());
            }
        }
    }

    public void checkArgToBase(Invoke callSite, int index, Pointer arg, Pointer base) {
        JMethod method = callSite.getMethodRef().resolve();
        for (var transfer : config.getTransfers()) {
            if (transfer.method().equals(method) && transfer.from() == index && transfer.to() == TaintTransfer.BASE) {
                addCFGEdge(arg, base, transfer.type());
            }
        }
    }

    public void checkArgToResult(Invoke callSite, int index, Pointer arg, Pointer result) {
        JMethod method = callSite.getMethodRef().resolve();
        for (var transfer : config.getTransfers()) {
            if (transfer.method().equals(method) && transfer.from() == index && transfer.to() == TaintTransfer.RESULT) {
                addCFGEdge(arg, result, transfer.type());
            }
        }
    }

    public void checkSink(Invoke callSite, int index, CSVar pointer) {
        JMethod method = callSite.getMethodRef().resolve();
        Sink sink = new Sink(method, index);
        if (config.getSinks().contains(sink)) {
            sinkMap.put(new CallSiteIndex(callSite, index), pointer);
        }
    }

    public void onFinish() {
        PointerAnalysisResult result = solver.getResult();
        sinkMap.forEach((sink, pointer) -> {
            Set<CSObj> pts = result.getPointsToSet(pointer);
            pts.forEach(csobj -> {
                Obj obj = csobj.getObject();
                if (manager.isTaint(obj)) {
                    taintFlows.add(new TaintFlow(manager.getSourceCall(obj), sink.callSite(), sink.index()));
                }
            });
        });
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }
}