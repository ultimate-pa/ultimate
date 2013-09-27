/*
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for 
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 * 
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package pea;

import pea.modelchecking.armc.ARMCWriter.ARMCString;


/**
 * RelationDecision is an extension of BooleanDecision and represents a simple relational
 * statement.
 * Currently (in the context of the PEA toolkit with its export functions to, e.g., ARMC)
 * we support expression with basic arithmetical relations: <,>,<=,>=,=,!=.
 * For instance, the boolean expression a < b+c can be processed (b+c is considered as a constant).
 * More complicated expressions are not supported. Please use ZDecision instead.
 *
 * @author jfaber
 *
 */
public class RelationDecision extends BooleanDecision {
   
    public enum Operator{
    /* Constants for supported operators in BooleanDecisions.
     * We use the ARMC strings as default where possible.
     */
        PRIME  ("'"),
        LESS   (ARMCString.LESS),
        GREATER(ARMCString.GREATER),      
        LEQ    (ARMCString.LEQ),    
        GEQ    (ARMCString.GEQ),
        EQUALS (ARMCString.EQUALS),
        PLUS   (ARMCString.PLUS),
        MINUS  (ARMCString.MINUS),
        MULT   (ARMCString.MULT),
        DIV    (ARMCString.DIV),
        NEQ    ("!=");
        
        String op;
        
        private Operator(String op){
            this.op = op;
        }
        
        public String toString(){
            return op;
        }
    
    }
    
    
    String leftExpr;
    String rightExpr;
    Operator op;
    

    /**
     * @param leftExpr
     * @param op
     * @param rightExpr
     */
    public RelationDecision(String leftExpr, Operator op,
            String rightExpr) {
        super(leftExpr + op + rightExpr);
        if(leftExpr == null || rightExpr == null){
            System.err.println();
        }
        this.leftExpr = leftExpr;
        this.op = op;
        this.rightExpr = rightExpr;
    }

    /**
     * Create an boolean constraint.
     * @param var the condition that must hold.
     */
    public static CDD create(String leftExpr, Operator op, String rightExpr) {
	if(op.equals(Operator.GEQ)){
	    return CDD.create(new RelationDecision(leftExpr, Operator.LESS, rightExpr), CDD.falseChilds);
	}else if(op.equals(Operator.GREATER)){
	    return CDD.create(new RelationDecision(leftExpr, Operator.LEQ, rightExpr), CDD.falseChilds);
	}
        return CDD.create(new RelationDecision(leftExpr, op, rightExpr), CDD.trueChilds);
    }
    
   /**
     * Returns a RelationDecision for the given operator and the given
     * expressions contained in the array exprs.
     * 
     * @param exprs
     *          Left and right expression for the given binary operator.
     *          Throws a IllegalArgumentException() when exprs has not exactly two
     *          entries.
     * @param op
     *          The binary operator for the expression.
     * @return
     *          RelationDecision for the operator and the given expressions.
     */
    public static CDD create(String[] exprs, Operator op) {
        if(exprs.length != 2){
            throw new IllegalArgumentException();
        }
        return RelationDecision.create(exprs[0],op,exprs[1]);
    }

    public boolean equals(Object o) {
	if (!(o instanceof BooleanDecision))
	    return false;
	if (!var.equals(((BooleanDecision) o).var))
	    return false;
	return true;
    }

    public int compareTo(Object o) {
	if (!(o instanceof BooleanDecision))
	    return 1;

	return var.compareTo(((BooleanDecision) o).var);
    }
    
    /**
     * @return Returns the var.
     */
    public String getVar() {
        return var;
    }
    
    public String toString(int child) {
	if(child != 0){
	    switch (op) {
	    case LESS:
	        return leftExpr + Operator.GEQ + rightExpr;
            case GREATER:
                return leftExpr + Operator.LEQ + rightExpr;
            case LEQ:
                return leftExpr + Operator.GREATER + rightExpr;
            case GEQ:
                return leftExpr + Operator.LESS + rightExpr;
            case EQUALS:
                return leftExpr + Operator.NEQ + rightExpr;
            case NEQ:
                return leftExpr + Operator.EQUALS + rightExpr;
            }
	}
	return var;        

    }

    public String toUppaalString(int child) {
        return "true";
    }

    @Override
    public Decision prime() {
        String expr1 = this.leftExpr.replaceAll("([a-zA-Z_])(\\w*)", "$1$2" + RelationDecision.PRIME); 
        String expr2 = this.rightExpr.replaceAll("([a-zA-Z_])(\\w*)", "$1$2" + RelationDecision.PRIME); 
        return (new RelationDecision(expr1,this.op,expr2));
    }
    
    @Override
    public Decision unprime() {
    	String expr1 = this.leftExpr;
    	String expr2 = this.rightExpr;
    	if (this.leftExpr.endsWith(PRIME)){
    		expr1 = this.leftExpr.substring(0,this.leftExpr.length()-1); 
    	}
    	if (this.rightExpr.endsWith(PRIME)){
    		expr2 = this.rightExpr.substring(0,this.rightExpr.length()-1); 
        }
        return (new RelationDecision(expr1,this.op,expr2));
    }
}