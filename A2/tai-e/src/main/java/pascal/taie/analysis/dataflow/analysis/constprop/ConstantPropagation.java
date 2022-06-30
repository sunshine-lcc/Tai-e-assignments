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
        // TODO - finish me
        var cpfact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            cpfact.update(param, Value.getNAC());
        }
        return cpfact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        var cpfact = new CPFact();
        return cpfact;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (var key : fact.keySet()) {
            target.update(key, this.meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isConstant() && v2.isUndef()) {
            return v1;
        } else if (v1.isUndef() && v2.isConstant()) {
            return v2;
        } else if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return v1;
            } else {
                return Value.getNAC();
            }
        } else {
            return Value.getUndef();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact in_copy = in.copy();
        if (stmt.getDef().isPresent()) {
            in_copy.remove((Var) stmt.getDef().get());
        }
        for (RValue n : stmt.getUses()) {
            if (stmt.getDef().isPresent() && canHoldInt((Var) stmt.getDef().get())) {
                var new_val = this.evaluate(n, in_copy);
                in_copy.update((Var) stmt.getDef().get(), new_val);
            }
        }
        out.copyFrom(in_copy);
        return false;
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
        // TODO - finish me
        Value ret = null;
        if (exp instanceof Var) {
            ret = in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {
            ret = Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {
            BinaryExp bin_expr = (BinaryExp) exp;
            Var op1 = bin_expr.getOperand1();
            Var op2 = bin_expr.getOperand2();
            if (in.get(op1).isConstant() && in.get(op2).isConstant()) {
                int op1_int = in.get(op1).getConstant();
                int op2_int = in.get(op2).getConstant();
                switch (bin_expr.getOperator().toString()) {
                    case "*":
                        ret = Value.makeConstant(op1_int * op2_int);
                        break;
                    case "+":
                        ret = Value.makeConstant(op1_int + op2_int);
                        break;
                    case "-":
                        ret = Value.makeConstant(op1_int - op2_int);
                        break;
                    case "/":
                        if (op2_int == 0) {
                            ret = Value.getUndef();
                        } else {
                            ret = Value.makeConstant(op1_int / op2_int);
                        }
                        break;
                    case ">>":
                        ret = Value.makeConstant(op1_int >> op2_int);
                        break;
                    case "<<":
                        ret = Value.makeConstant(op1_int << op2_int);
                        break;
                    case ">>>":
                        ret = Value.makeConstant(op1_int >>> op2_int);
                        break;
                    case "==":
                        if (op1_int == op2_int) {
                            ret = Value.makeConstant(1);
                        } else {
                            ret = Value.makeConstant(0);
                        }
                        break;
                    case "!=":
                        if (op1_int != op2_int) {
                            ret = Value.makeConstant(1);
                        } else {
                            ret = Value.makeConstant(0);
                        }
                        break;
                    case "<":
                        if (op1_int < op2_int) {
                            ret = Value.makeConstant(1);
                        } else {
                            ret = Value.makeConstant(0);
                        }
                        break;
                    case ">":
                        if (op1_int > op2_int) {
                            ret = Value.makeConstant(1);
                        } else {
                            ret = Value.makeConstant(0);
                        }
                        break;
                    case "<=":
                        if (op1_int <= op2_int) {
                            ret = Value.makeConstant(1);
                        } else {
                            ret = Value.makeConstant(0);
                        }
                        break;
                    case ">=":
                        if (op1_int >= op2_int) {
                            ret = Value.makeConstant(1);
                        } else {
                            ret = Value.makeConstant(0);
                        }
                        break;
                    case "|":
                        ret = Value.makeConstant(op1_int | op2_int);
                        break;
                    case "&":
                        ret = Value.makeConstant(op1_int & op2_int);
                        break;
                    case "^":
                        ret = Value.makeConstant(op1_int ^ op2_int);
                        break;
                        default:
                            ret = Value.getUndef();
                            break;
                }
            } else if (in.get(op1).isNAC() || in.get(op2).isNAC()) {
                ret = Value.getNAC();
            } else {
                ret = Value.getUndef();
            }
        } else {
            throw new UnsupportedOperationException("Unknown expression");
        }
        return ret;
    }
}
