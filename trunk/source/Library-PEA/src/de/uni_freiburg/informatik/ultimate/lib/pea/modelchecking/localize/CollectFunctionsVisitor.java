/* $Id$
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 * 
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
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

package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.localize;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.BindSelExpr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;

/**
 * CollectFunctionsVisitor is a visitor class for Z terms that collects all functions
 * used in the term and allowed in Localize export.
 * In particular, it collects all extension functions, base functions, relations,
 * and the cardinalities of extension functions in Maps containing function names and types or in sets.
 * It only allows extension functions previously declared in a given map of function names and types.
 *
 * The generated collections can be accessed via getter methods after processing a number
 * of term objects.
 *
 * @author jfaber
 *
 */
public class CollectFunctionsVisitor implements
    ZNameVisitor,
    TermVisitor,
    ApplExprVisitor {

    
    /**
     * A set containing all base operators or functions that are supported by Localize.
     */
    private static final Set<String> ALL_BASE_FUNCTIONS;

    /**
     * A set containing all relation operators that are supported by Localize.
     */
    private static final Set<String> ALL_RELATIONS;
    
    static {
        ALL_BASE_FUNCTIONS = new HashSet<>();
        ALL_BASE_FUNCTIONS.add(ZString.PLUS);
        ALL_BASE_FUNCTIONS.add(ZString.MINUS);
        ALL_BASE_FUNCTIONS.add(ZString.MULT);
        ALL_BASE_FUNCTIONS.add(LocalizeWriter.Z_DIV);

        ALL_RELATIONS= new HashSet<>();
        ALL_RELATIONS.add(ZString.LEQ);
        ALL_RELATIONS.add(ZString.LESS);
        ALL_RELATIONS.add(ZString.GEQ);
        ALL_RELATIONS.add(ZString.GREATER);
// EQUALS and NEQ are not considered to be relations
//        ALL_RELATIONS.add(ZString.EQUALS);
//        ALL_RELATIONS.add(ZString.NEQ);
    }
    
    
    /**
     * Map containing type declarations for extension functions that are given in the constructor
     * of this visitor.
     */
    private final Map<String,String> declarations;
    
    
    /**
     * A map containing names and types of extension functions collected in several applications of
     * this visitor.
     */
    private final Map<String,String> extFunctions = new HashMap<>();

    /**
     * A set containing names of base functions collected in several applications of
     * this visitor.
     */
    private final Set<String> baseFunctions = new HashSet<>();
    
    /**
     * A set containing names relations collected in several applications of
     * this visitor.
     */
    private final Set<String> relations = new HashSet<>();


    /**
     * Constructor assigning a map of declared variables with types.
     * @param variables
     *          a given map of variables to types
     */
    public CollectFunctionsVisitor(final Map<String, String> variables) {
        declarations = variables;
    }

    /*
     * (non-Javadoc)
     * 
     * @see net.sourceforge.czt.base.visitor.TermVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
     */
    @Override
	@SuppressWarnings("unchecked")
    public Object visitTerm(final Term zedObject) {
/*        StringWriter sw = new StringWriter();
        PrintUtils.printUnicode(zedObject, sw, sectionInfo, ZWrapper.getSectionName());
        if(sw.toString().contains("dctag")) {
            System.out.println();
            System.out.println("term start");
            System.out.println();
            System.out.println(sw);
            System.out.println();
            System.out.println(" end");
            System.out.println();
        }
*/
        final Object[] children = zedObject.getChildren();
            for (final Object child : children) {
                    if (child instanceof Term) {
                            ((Term) child).accept(this);
                    }
            }
            return null;
    }
    
    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ZNameVisitor#visitZName(net.sourceforge.czt.z.ast.ZName)
     */
    @Override
    public Object visitZName(final ZName zname) {
/*
        StringWriter sw = new StringWriter();
        PrintUtils.printUnicode(zname, sw, sectionInfo, ZWrapper.getSectionName());
        if(sw.toString().contains("dctag")) {
            System.out.println();
            System.out.println("zname start");
            System.out.println();
            System.out.println(sw);
            System.out.println();
            System.out.println(" end");
            System.out.println();
        }
*/
        final OperatorName opname = zname.getOperatorName();
        if(opname!= null){
            final String name = opname.getWord().replaceAll(ZString.ARG_TOK, "");
            if(ALL_RELATIONS.contains(name)){
//                if(name.equals(ZString.NEQ))
//                    relations.add(LocalizeString.EQUALS);
//                else
                relations.add(LocalizeWriter.operatorFor(name));
            }
            //            Functions.put(name + strokes,declarations.get(name));
        }else {
            final String nameWithoutStrokes = zname.getWord();
            if(declarations.containsKey(nameWithoutStrokes) && !extFunctions.containsKey(zname.toString())){
                extFunctions.put(zname.toString(),declarations.get(nameWithoutStrokes));
            }
        }
        
        return null;
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ApplExprVisitor#visitApplExpr(net.sourceforge.czt.z.ast.ApplExpr)
     */
    @SuppressWarnings("unchecked")
    @Override
    public Object visitApplExpr(final ApplExpr expr) {
/*
        StringWriter sw = new StringWriter();
        PrintUtils.printUnicode(expr, sw, sectionInfo, ZWrapper.getSectionName());
        if(sw.toString().contains("dctag")) {
            System.out.println();
            System.out.println("ApplExpr start");
            System.out.println();
            System.out.println(sw);
            System.out.println();
            System.out.println(" end");
            System.out.println();
        }
*/
        ZName zname = null;
        if(expr.getLeftExpr() instanceof RefExpr) {
			zname = ((RefExpr) expr.getLeftExpr()).getZName();
		} else if(expr.getLeftExpr() instanceof BindSelExpr) {
			zname = ((BindSelExpr) expr.getLeftExpr()).getZName();
		} else if(expr.getLeftExpr() instanceof ApplExpr) {
            expr.getLeftExpr().accept(this);
            expr.getRightExpr().accept(this);
            return null;
        }
        final String name = zname.toString();
        final String nameWithoutStrokes = zname.getWord();
        // We only allow functions as extension functions that are declared correctly.
        if(declarations.containsKey(nameWithoutStrokes) && !extFunctions.containsKey(name)){
            extFunctions.put(name,declarations.get(nameWithoutStrokes));
        }else if(!extFunctions.containsKey(name)){
            final String opname = name.replaceAll(ZString.ARG_TOK, "");
            if(ALL_BASE_FUNCTIONS.contains(opname)) {
				baseFunctions.add(opname);
			} else { // We do not know the function and, hence, raise an error.
                throw new LocalizeException(LocalizeException.UNKNOWN_FUNCTION_SYMBOL +
                          name);
            }
        }

        expr.getRightExpr().accept(this);
                
        return null;
    }
    
    

    /**
     * @return Returns the extFunctions.
     */
    public Map<String,String> getExtFunctions() {
        return extFunctions;
    }

    /**
     * @return Returns the baseFunctions.
     */
    public Set<String> getBaseFunctions() {
        return baseFunctions;
    }

    /**
     * @return Returns the relations.
     */
    public Set<String> getRelations() {
        return relations;
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.MemPredVisitor#visitMemPred(net.sourceforge.czt.z.ast.MemPred)
     
    @Override
    public Object visitMemPred(MemPred pred) {
        if(pred.getRightExpr() instanceof RefExpr) {
            StringWriter sw = new StringWriter();
            PrintUtils.printUnicode(pred, sw, sectionInfo, ZWrapper.getSectionName());
            if(sw.toString().contains("dctag")) {
                System.out.println();
                System.out.println("RefExpr start");
                System.out.println();
                System.out.println(sw);
                System.out.println();
                System.out.println(" end");
                System.out.println();
            }
        }
        Object[] children = pred.getChildren();
        for (Object child : children) {
                if (child instanceof Term) {
                        ((Term) child).accept(this);
                }
        }
        return null;
    }*/



}
