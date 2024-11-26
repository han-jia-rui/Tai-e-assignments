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
import pascal.taie.analysis.dataflow.inter.InterConstantPropagation;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.*;

public class ConstantPropagation extends AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    private final InterConstantPropagation interCP;

    private final Map<Object, RelevantStmts> relevantStmtsMap = new HashMap<>();

    private static class RelevantStmts {
        private Set<StoreField> storeFields = Set.of();
        private Set<StoreArray> storeArrays = Set.of();

        private static <T> Set<T> unmodifiable(Set<T> set) {
            return set.isEmpty() ? set : Collections.unmodifiableSet(set);
        }

        private Set<StoreField> getStoreFields() {
            return unmodifiable(storeFields);
        }

        private void addStoreField(StoreField storeField) {
            if (storeFields.isEmpty()) {
                storeFields = new HashSet<>();
            }
            storeFields.add(storeField);
        }

        private Set<StoreArray> getStoreArrays() {
            return unmodifiable(storeArrays);
        }

        private void addStoreArray(StoreArray storeArray) {
            if (storeArrays.isEmpty()) {
                storeArrays = new HashSet<>();
            }
            storeArrays.add(storeArray);
        }
    }

    public void addStoreFields(FieldRef fieldRef, StoreField storeField) {
        RelevantStmts relevantStmts = relevantStmtsMap.get(fieldRef);
        if (relevantStmts == null) {
            relevantStmts = new RelevantStmts();
            relevantStmtsMap.put(fieldRef, relevantStmts);
        }
        relevantStmts.addStoreField(storeField);
    }

    public Set<StoreField> getStoreFields(FieldRef fieldRef) {
        RelevantStmts relevantStmts = relevantStmtsMap.get(fieldRef);
        if (relevantStmts == null) {
            relevantStmts = new RelevantStmts();
            relevantStmtsMap.put(fieldRef, relevantStmts);
        }
        return relevantStmts.getStoreFields();
    }

    public void addStoreFields(Var var, StoreField storeField) {
        RelevantStmts relevantStmts = relevantStmtsMap.get(var);
        if (relevantStmts == null) {
            relevantStmts = new RelevantStmts();
            relevantStmtsMap.put(var, relevantStmts);
        }
        relevantStmts.addStoreField(storeField);
    }

    public Set<StoreField> getStoreFields(Var var) {
        RelevantStmts relevantStmts = relevantStmtsMap.get(var);
        if (relevantStmts == null) {
            relevantStmts = new RelevantStmts();
            relevantStmtsMap.put(var, relevantStmts);
        }
        return relevantStmts.getStoreFields();
    }

    public void addStoreArrays(Var var, StoreArray storeArray) {
        RelevantStmts relevantStmts = relevantStmtsMap.get(var);
        if (relevantStmts == null) {
            relevantStmts = new RelevantStmts();
            relevantStmtsMap.put(var, relevantStmts);
        }
        relevantStmts.addStoreArray(storeArray);
    }

    public Set<StoreArray> getStoreArrays(Var var) {
        RelevantStmts relevantStmts = relevantStmtsMap.get(var);
        if (relevantStmts == null) {
            relevantStmts = new RelevantStmts();
            relevantStmtsMap.put(var, relevantStmts);
        }
        return relevantStmts.getStoreArrays();
    }

    public ConstantPropagation(AnalysisConfig config, InterConstantPropagation interCP) {
        super(config);
        this.interCP = interCP;
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
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (v1.isConstant() && v2.isConstant() && v2.getConstant() == v1.getConstant()) return v1;
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var newOut = in.copy();
        if (stmt instanceof AssignStmt<?, ?> def) {
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

    private class ExpProcessor implements ExpVisitor<Value> {
        CPFact currentFact;

        public ExpProcessor(CPFact in) {
            currentFact = in;
        }

        @Override
        public Value visitDefault(Exp exp) {
            return Value.getNAC();
        }

        @Override
        public Value visit(IntLiteral literal) {
            return Value.makeConstant(literal.getValue());
        }

        @Override
        public Value visit(Var var) {
            return currentFact.get(var);
        }

        @Override
        public Value visit(ConditionExp exp) {
            var v1 = currentFact.get(exp.getOperand1());
            var v2 = currentFact.get(exp.getOperand2());
            if (v1.isConstant() && v2.isConstant()) {
                int value1 = v1.getConstant();
                int value2 = v2.getConstant();
                return switch (exp.getOperator()) {
                    case EQ -> Value.makeConstant(value1 == value2 ? 1 : 0);
                    case NE -> Value.makeConstant(value1 != value2 ? 1 : 0);
                    case LT -> Value.makeConstant(value1 < value2 ? 1 : 0);
                    case LE -> Value.makeConstant(value1 <= value2 ? 1 : 0);
                    case GT -> Value.makeConstant(value1 > value2 ? 1 : 0);
                    case GE -> Value.makeConstant(value1 >= value2 ? 1 : 0);
                };
            }
            if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }

        @Override
        public Value visit(ShiftExp exp) {
            var v1 = currentFact.get(exp.getOperand1());
            var v2 = currentFact.get(exp.getOperand2());
            if (v1.isConstant() && v2.isConstant()) {
                int value1 = v1.getConstant();
                int value2 = v2.getConstant();
                return switch (exp.getOperator()) {
                    case SHL -> Value.makeConstant(value1 << value2);
                    case SHR -> Value.makeConstant(value1 >> value2);
                    case USHR -> Value.makeConstant(value1 >>> value2);
                };
            }
            if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }

        @Override
        public Value visit(BitwiseExp exp) {
            var v1 = currentFact.get(exp.getOperand1());
            var v2 = currentFact.get(exp.getOperand2());
            if (v1.isConstant() && v2.isConstant()) {
                int value1 = v1.getConstant();
                int value2 = v2.getConstant();
                return switch (exp.getOperator()) {
                    case AND -> Value.makeConstant(value1 & value2);
                    case OR -> Value.makeConstant(value1 | value2);
                    case XOR -> Value.makeConstant(value1 ^ value2);
                };
            }
            if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }

        @Override
        public Value visit(ArithmeticExp exp) {
            var v1 = currentFact.get(exp.getOperand1());
            var v2 = currentFact.get(exp.getOperand2());
            if (v2.isConstant() && v2.getConstant() == 0) {
                var op = exp.getOperator();
                if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) {
                    return Value.getUndef();
                }
            }
            if (v1.isConstant() && v2.isConstant()) {
                int value1 = v1.getConstant();
                int value2 = v2.getConstant();
                return switch (exp.getOperator()) {
                    case ADD -> Value.makeConstant(value1 + value2);
                    case SUB -> Value.makeConstant(value1 - value2);
                    case MUL -> Value.makeConstant(value1 * value2);
                    case DIV -> Value.makeConstant(value1 / value2);
                    case REM -> Value.makeConstant(value1 % value2);
                };
            }
            if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }

        @Override
        public Value visit(StaticFieldAccess fieldAccess) {
            Value value = Value.getUndef();
            Set<StoreField> storeFields = getStoreFields(fieldAccess.getFieldRef());
            for (var storeField : storeFields) {
                CPFact anotherFact = interCP.getOutFact(storeField);
                if (canHoldInt(storeField.getRValue())) {
                    value = meetValue(value, anotherFact.get(storeField.getRValue()));
                }
            }
            return value;
        }

        @Override
        public Value visit(InstanceFieldAccess fieldAccess) {
            Value value = Value.getUndef();
            Set<StoreField> storeFields = getStoreFields(fieldAccess.getBase());
            for (var storeField : storeFields) {
                if (!fieldAccess.getFieldRef().equals(storeField.getFieldRef()))
                    continue;
                CPFact anotherFact = interCP.getOutFact(storeField);
                if (canHoldInt(storeField.getRValue())) {
                    value = meetValue(value, anotherFact.get(storeField.getRValue()));
                }
            }
            return value;
        }

        @Override
        public Value visit(ArrayAccess arrayAccess) {
            Value value = Value.getUndef();
            Var i = arrayAccess.getIndex();
            Set<StoreArray> storeArrays = getStoreArrays(arrayAccess.getBase());
            for (var storeArray : storeArrays) {
                if (canHoldInt(storeArray.getRValue())) {
                    Var j = storeArray.getArrayAccess().getIndex();
                    CPFact anotherFact = interCP.getOutFact(storeArray);
                    if (currentFact.get(i).isUndef() || anotherFact.get(j).isUndef())
                        continue;
                    if (currentFact.get(i).isConstant() && anotherFact.get(j).isConstant()
                            && currentFact.get(i).getConstant() != anotherFact.get(j).getConstant())
                        continue;
                    value = meetValue(value, anotherFact.get(storeArray.getRValue()));
                }
            }
            return value;
        }
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public Value evaluate(Exp exp, CPFact in) {
        return exp.accept(new ExpProcessor(in));
    }
}
