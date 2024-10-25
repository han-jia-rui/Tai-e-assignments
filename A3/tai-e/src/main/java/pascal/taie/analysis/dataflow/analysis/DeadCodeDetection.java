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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import javax.swing.text.html.Option;
import java.util.Comparator;
import java.util.Set;
import java.util.HashSet;
import java.util.Stack;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);

        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> visited = new HashSet<>();
        Stack<Stmt> stack = new Stack<>();

        stack.push(cfg.getEntry());
        while (!stack.empty()) {
            Stmt current = stack.pop();
            if (visited.contains(current))
                continue;
            visited.add(current);

            if (current instanceof AssignStmt<?, ?> assignStmt) {
                RValue rValue = assignStmt.getRValue();
                LValue lValue = assignStmt.getLValue();
                SetFact<Var> lvFact = liveVars.getOutFact(current);
                if (lValue instanceof Var variable && hasNoSideEffect(rValue)
                        && !lvFact.contains(variable))
                    deadCode.add(current);
            }

            if (current instanceof If ifStmt) {
                CPFact cpFact = constants.getOutFact(current);
                Value value = ConstantPropagation.evaluate(ifStmt.getCondition(), cpFact);
                if (value.isConstant()) {
                    int constant = value.getConstant();
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(current)) {
                        if (constant == 1 && edge.getKind() == Edge.Kind.IF_TRUE)
                            stack.push(edge.getTarget());
                        if (constant == 0 && edge.getKind() == Edge.Kind.IF_FALSE)
                            stack.push(edge.getTarget());
                    }
                    continue;
                }
            }

            if (current instanceof SwitchStmt switchStmt) {
                CPFact cpFact = constants.getOutFact(current);
                Value value = cpFact.get(switchStmt.getVar());
                if (value.isConstant()) {
                    int constant = value.getConstant();
                    boolean match = false;
                    for (var caseTargets : switchStmt.getCaseTargets())
                        if (constant == caseTargets.first()) {
                            match = true;
                            stack.push(caseTargets.second());
                            break;
                        }
                    if (!match)
                        stack.push(switchStmt.getDefaultTarget());
                    continue;
                }
            }
            for (var next : cfg.getSuccsOf(current))
                if (!visited.contains(next))
                    stack.push(next);
        }
        for (var stmt : ir.getStmts()) {
            if (!visited.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
