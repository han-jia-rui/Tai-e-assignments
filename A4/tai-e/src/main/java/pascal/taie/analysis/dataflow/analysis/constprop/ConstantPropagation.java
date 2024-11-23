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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var fact = new CPFact();
        var param_list = cfg.getIR().getParams();
        for (var param : param_list) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (var key : fact.keySet()) {
            target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isUndef())
            return v2;
        if (v2.isUndef())
            return v1;
        if (v1.isConstant() && v2.isConstant() && v2.getConstant() == v1.getConstant())
            return v1;
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var newOut = in.copy();
        if (stmt instanceof DefinitionStmt<?, ?> def) {
            var lhs = def.getLValue();
            var rhs = def.getRValue();
            if (lhs instanceof Var lVar && canHoldInt(lVar)) {
                newOut.update(lVar, evaluate(rhs, in));
            }
        }
        return out.copyFrom(newOut);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof Var variable) {
            return in.get(variable);
        }
        if (exp instanceof BinaryExp binaryExp) {
            var v1 = binaryExp.getOperand1();
            var v2 = binaryExp.getOperand2();

            if (exp instanceof ArithmeticExp arithmeticExp && in.get(v2).isConstant()) {
                var op = arithmeticExp.getOperator();
                if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) {
                    if (in.get(v2).getConstant() == 0) {
                        return Value.getUndef();
                    }
                }
            }

            if (in.get(v1).isConstant() && in.get(v2).isConstant()) {
                int value1 = in.get(v1).getConstant();
                int value2 = in.get(v2).getConstant();
                if (exp instanceof ArithmeticExp arithmeticExp) {
                    var op = arithmeticExp.getOperator();
                    return switch (op) {
                        case ADD -> Value.makeConstant(value1 + value2);
                        case SUB -> Value.makeConstant(value1 - value2);
                        case MUL -> Value.makeConstant(value1 * value2);
                        case DIV -> Value.makeConstant(value1 / value2);
                        case REM -> Value.makeConstant(value1 % value2);
                    };
                }
                if (exp instanceof ConditionExp conditionExp) {
                    var op = conditionExp.getOperator();
                    return switch (op) {
                        case EQ -> Value.makeConstant(value1 == value2 ? 1 : 0);
                        case NE -> Value.makeConstant(value1 != value2 ? 1 : 0);
                        case LT -> Value.makeConstant(value1 < value2 ? 1 : 0);
                        case LE -> Value.makeConstant(value1 <= value2 ? 1 : 0);
                        case GT -> Value.makeConstant(value1 > value2 ? 1 : 0);
                        case GE -> Value.makeConstant(value1 >= value2 ? 1 : 0);
                    };
                }
                if (exp instanceof ShiftExp shiftExp) {
                    var op = shiftExp.getOperator();
                    return switch (op) {
                        case SHL -> Value.makeConstant(value1 << value2);
                        case SHR -> Value.makeConstant(value1 >> value2);
                        case USHR -> Value.makeConstant(value1 >>> value2);
                    };
                }
                if (exp instanceof BitwiseExp bitwiseExp) {
                    var op = bitwiseExp.getOperator();
                    return switch (op) {
                        case AND -> Value.makeConstant(value1 & value2);
                        case OR -> Value.makeConstant(value1 | value2);
                        case XOR -> Value.makeConstant(value1 ^ value2);
                    };
                }
            }

            if (in.get(v1).isNAC() || in.get(v2).isNAC()) {
                return Value.getNAC();
            }

            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
