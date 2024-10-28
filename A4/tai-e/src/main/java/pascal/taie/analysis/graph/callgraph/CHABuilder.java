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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> queue = new LinkedList<>();
        queue.add(entry);
        while (!queue.isEmpty()) {
            JMethod current = queue.poll();
            if (!callGraph.contains(current)) {
                callGraph.addReachableMethod(current);
                current.getIR().forEach(stmt -> {
                    if (stmt instanceof Invoke invoke) {
                        Set<JMethod> targets = resolve(invoke);
                        targets.forEach(method -> {
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method));
                            queue.add(method);
                        });
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> targets = new HashSet<>();
        CallKind callKind = CallGraphs.getCallKind(callSite);
        MethodRef methodRef = callSite.getMethodRef();
        JClass jclass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();
        switch (callKind) {
            case STATIC -> targets.add(jclass.getDeclaredMethod(subsignature));
            case SPECIAL -> targets.add(dispatch(jclass, subsignature));
            case VIRTUAL, INTERFACE -> {
                Queue<JClass> queue = new LinkedList<>();
                queue.add(jclass);
                while (!queue.isEmpty()) {
                    JClass current = queue.poll();
                    targets.add(dispatch(current, subsignature));
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(current));
                    queue.addAll(hierarchy.getDirectImplementorsOf(current));
                    queue.addAll(hierarchy.getDirectSubclassesOf(current));
                }
            }
        }
        targets.remove(null);
        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod target = jclass.getDeclaredMethod(subsignature);
        if (target != null && !target.isAbstract())
            return target;
        JClass superclass = jclass.getSuperClass();
        if (superclass != null)
            return dispatch(superclass, subsignature);
        return null;
    }
}
