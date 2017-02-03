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

import java.io.StringWriter;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.localize.LocalizeWriter.LocalizeString;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.TermToZCDDVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZTerm;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZWrapper;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.print.oz.PrintUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Exists1Pred;
import net.sourceforge.czt.z.ast.ExistsPred;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.FalsePred;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.IffPred;
import net.sourceforge.czt.z.ast.ImpliesPred;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ParenAnn;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.Exists1PredVisitor;
import net.sourceforge.czt.z.visitor.ExistsPredVisitor;
import net.sourceforge.czt.z.visitor.ExprPredVisitor;
import net.sourceforge.czt.z.visitor.FalsePredVisitor;
import net.sourceforge.czt.z.visitor.ForallPredVisitor;
import net.sourceforge.czt.z.visitor.IffPredVisitor;
import net.sourceforge.czt.z.visitor.ImpliesPredVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.NegPredVisitor;
import net.sourceforge.czt.z.visitor.NumExprVisitor;
import net.sourceforge.czt.z.visitor.TruePredVisitor;

/**
 * LocalizeZVisitor is visitor for Z predicates that transforms a Z term into a string. The visitor does
 * not visit all Z construct itself but uses the czt unicode output for general Z terms. This
 * visitor visit only the terms where the usual unicode representation does not help 
 * for Localize output.  
 *
 * @author jfaber
 *
 */
public class LocalizeZVisitor implements
    TermVisitor<StringBuffer>,
    ForallPredVisitor<StringBuffer>,
    NegPredVisitor<StringBuffer>,
    NumExprVisitor<StringBuffer>,
    ExistsPredVisitor<StringBuffer>,
    Exists1PredVisitor<StringBuffer>,
    ExprPredVisitor<StringBuffer>,
    FalsePredVisitor<StringBuffer>,
    TruePredVisitor<StringBuffer>,
    ImpliesPredVisitor<StringBuffer>,
    IffPredVisitor<StringBuffer>,
    MemPredVisitor<StringBuffer>,
    ApplExprVisitor<StringBuffer>
    {

    
    /**
     * Used for error reports.
     */
    protected static final String MEMBERSHIP_PREDICATE = "Membership predicate";

    /**
     * SectionInfo which is necessary to print the unicode representation of a term.
     */
    protected SectionInfo sectionInfo;
    
    /**
     * Constant symbols that do not need to be primed.
     */
    protected Set<String> constants;

    
    /**
     * A flag that is set to true if a number expression needs enclosing parantheses.
     */
//    protected boolean needsParen = false;

    /**
     * The map contains declared variable names together with their types.
     */
    protected Map<String, String> declarations;
    
    /**
     * The visitor is used to generate CDDs from term objects which is necessary, e.g., in 
     * visitForAllPred.
     */
    protected TermToZCDDVisitor toCDDVisitor;

    protected int quantificationLevel;

    /**
     * A LocalizeWriter that is used to write CDD clauses to the Localize output
     * file.
     */
    protected LocalizeWriter localizeWriter;

    private final Map<String, Integer> freeTypes;

    private final Map<String, String> nullPointers;

    private final boolean useClausesForm;
    
    public LocalizeZVisitor(ZTerm term, Set<String> constants,Map<String,String> declarations,
            Map<String, Integer> freeTypes,
            Map<String, String> nullPointers, LocalizeWriter writer, boolean useClausesForm) {
        sectionInfo = term.getSectionInfo();
        toCDDVisitor = new TermToZCDDVisitor(term);
        this.constants = constants;
        this.declarations = declarations;
        this.freeTypes = freeTypes;
        this.nullPointers = nullPointers;
        localizeWriter = writer;
        this.useClausesForm = useClausesForm;
        quantificationLevel = 0;
    }

       public LocalizeZVisitor(ZTerm term, Set<String> constants,Map<String,String> declarations,
            Map<String, Integer> freeTypes,
            Map<String, String> nullPointers, LocalizeWriter writer) {
           this(term,constants, declarations, freeTypes, nullPointers, writer, true);
       }
           
    /* (non-Javadoc)
     * @see net.sourceforge.czt.base.visitor.TermVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
     */
    @Override
    public StringBuffer visitTerm(Term zedObject) {
        removePrimesFromConstants(zedObject);
        final StringWriter sw = new StringWriter();
        PrintUtils.print(zedObject, sw, (SectionManager) sectionInfo, ZWrapper.getSectionName(), Markup.UNICODE);
        String result = sw.toString().trim();
        //if(result.contains("snil"))
        //    System.out.println(result);
        //if(nullPointers.containsKey(result))
        for(final String np : nullPointers.keySet()){
            if(result.contains(np)) {
				result = result.replace(np, nullPointers.get(np));
			}
        }
//        if(result.startsWith(LocalizeString.NUMPREFIX))
//            result = result.substring(1);
        return new StringBuffer(result);
    }

 
    /**
     * Removes prime symbols "'" which are wrongly added to constant symbols during
     * the generation of a transition constraint system from a Phase Event Automaton.
     * 
     * 
     * Attention: additionally removes NUMPREFIX from names.
     * TODO refactor to have this desired side-effect in an appropriate method and to
     * keep this method side-effect free.
     * 
     * @param zedObject
     *          The Z term to be modified by removing prime symbols.
     */
    private void removePrimesFromConstants(Term zedObject) {
        if(zedObject instanceof RefExpr) {
            final ZName name = ((RefExpr)zedObject).getZName();
            if(name.getWord().startsWith(LocalizeString.NUMPREFIX)){
                name.setWord(name.getWord().substring(1));
            }
        }
        if(zedObject instanceof ZName) {
            final ZName name = (ZName)zedObject;
            if(constants.contains(name.getWord())){
                name.setStrokeList(new ZFactoryImpl().createZStrokeList());
            }
        } else {
            final Object[] children = zedObject.getChildren();
            for (final Object child : children) {
                if (child instanceof Term) {
                    removePrimesFromConstants((Term) child);
                }
            }
        }
    }


    
    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ForallPredVisitor#visitForallPred(net.sourceforge.czt.z.ast.ForallPred)
     */
    @Override
    public StringBuffer visitForallPred(ForallPred forallPred) {
        
        //Translation of NEQ is now done in TermToCDDVisitor
        /* NOT ... = ... which is done in TransformNEQsVisitor
           TransformNEQsVisitor transformNEQs = new TransformNEQsVisitor();
           ForallPred forallPred = (ForallPred) pred.accept(transformNEQs); */
        
        
        final StringBuffer prefix = new StringBuffer();
        final StringBuffer sw = new StringBuffer();
        if(++quantificationLevel > 1) {
            quantificationLevel--;
            throw new LocalizeException(LocalizeException.NESTED_QUANTIFICATION);
        }
        prefix.append(LocalizeString.LPAREN + LocalizeString.FORALL + " ");
        final ZSchText schema = forallPred.getZSchText();
        int i = schema.getZDeclList().size();
        for (final Decl decl : schema.getZDeclList()) {
            --i;
            if(decl instanceof VarDecl){
                int j = ((VarDecl)decl).getZNameList().size();
                final Expr typeExpr = ((VarDecl)decl).getExpr();
                final String type = typeExpr.accept(this).toString().trim();
                if(!declarations.containsValue(type) &&
                        !type.equals(LocalizeWriter.Z_REAL_TYPE) &&
                        !type.equals(ZString.NUM) &&
                        !freeTypes.containsKey(type)) {
					throw new LocalizeException(LocalizeException.UNSUPPORTED_QUANTIFICATION + 
                            "(use " + LocalizeWriter.Z_REAL_TYPE + 
                            ", " + ZString.NUM + " or a free type): " + type);
				}
                for (final Name name : ((VarDecl)decl).getZNameList()) {
                    --j;
                    prefix.append(name);
                    if(i > 0 || j > 0) {
						prefix.append(",");
					}
                }
            }
        }
        //prefix.append(schema.getDeclList().accept(this)).append("). ");
        prefix.append(LocalizeString.RPAREN + ". ");
        
        //Production of FORALL predicates
        //1. tranform schema predicates to CDDs
        CDD antecedent = CDD.TRUE,
            implication;
        if(schema.getPred() != null) {
			antecedent = schema.getPred().accept(toCDDVisitor);
		}
        implication = antecedent.negate().or(forallPred.getPred().accept(toCDDVisitor));
        
        //2. CDDs to conjunctive normal form
        final CDD[] cnf = implication.toCNF();
        
        //3. new forall line for every disjunction term in the CNF
        for (int j = 0; j < cnf.length; j++) {

            if(j!=0) {
				sw.append(LocalizeString.INDENT);
			} 
            //4. build FORALL expression: prefix negatives --> positives
            sw.append(prefix);

            //5. split CDD in disjunction in negated and non-negated CDDs,
            //which is done in writeClauseToStringBuffer
            final StringWriter writer = new StringWriter();
            if(useClausesForm) {
				localizeWriter.writeClauseToWriter(cnf[j],writer);
			} else {
				localizeWriter.writeClauseAsDisjunction(cnf[j],writer);
			}
            sw.append(writer);
            if(j+1 < cnf.length) {
				sw.append(";\n");
			}
        }

            
        //if(schema.getPred() != null)
        //    sw.append(schema.getPred().accept(this));
        //sw.append(" --> ");
        //sw.append(forallPred.getPred().accept(this));
        
        quantificationLevel--;
        return sw;
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.NegPredVisitor#visitNegPred(net.sourceforge.czt.z.ast.NegPred)
     */
    @Override
    public StringBuffer visitNegPred(NegPred pred) {
        final StringBuffer sw = new StringBuffer(LocalizeString.NOT).append("(");
        sw.append(pred.getPred().accept(this)).append(")");
        return sw;
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.AndPredVisitor#visitAndPred(net.sourceforge.czt.z.ast.AndPred)
     */
//    @Override
//    public StringBuffer visitAndPred(AndPred andPred) {
//        StringBuffer sw = new StringBuffer();
//        sw.append(andPred.getLeftPred().accept(this));
//        sw.append(", ");
//        return sw.append(andPred.getRightPred().accept(this));
//    }



 


    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ExistsPredVisitor#visitExistsPred(net.sourceforge.czt.z.ast.ExistsPred)
     */
    @Override
    public StringBuffer visitExistsPred(ExistsPred pred) {
        throw new LocalizeException(LocalizeException.PREDICATE_TYPE_NOT_SUPPORTED
                + ExistsPred.class
                + "\n" + pred.toString());
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.Exists1PredVisitor#visitExists1Pred(net.sourceforge.czt.z.ast.Exists1Pred)
     */
    @Override
    public StringBuffer visitExists1Pred(Exists1Pred pred) {
        throw new LocalizeException(LocalizeException.PREDICATE_TYPE_NOT_SUPPORTED
                + Exists1Pred.class
                + "\n" + pred.toString());
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ExprPredVisitor#visitExprPred(net.sourceforge.czt.z.ast.ExprPred)
     */
    @Override
    public StringBuffer visitExprPred(ExprPred pred) {
      final StringWriter sw = new StringWriter();
      PrintUtils.print(pred, sw, (SectionManager) sectionInfo, ZWrapper.getSectionName(), Markup.UNICODE);
      throw new LocalizeException(LocalizeException.UNEXPECTED_EXPRESSION
              + "\n" + sw.toString());
//        StringWriter sw = new StringWriter();
//        PrintUtils.printUnicode(pred, sw, sectionInfo, ZWrapper.getSectionName());
//        return new StringBuffer(sw.toString().trim());
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.FalsePredVisitor#visitFalsePred(net.sourceforge.czt.z.ast.FalsePred)
     */
    @Override
    public StringBuffer visitFalsePred(FalsePred pred) {
        // Normally, false conjunctions are reduced by the CDD representation of 
        // the constraint, so we de not need to handle them here.
        throw new LocalizeException(LocalizeException.PREDICATE_TYPE_NOT_SUPPORTED
                + FalsePred.class
                + "\n" + pred.toString());
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.TruePredVisitor#visitTruePred(net.sourceforge.czt.z.ast.TruePred)
     */
    @Override
    public StringBuffer visitTruePred(TruePred arg0) {
        // In localize we can simple omit the true predicate in a conjunction.
        return new StringBuffer("");
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ImpliesPredVisitor#visitImpliesPred(net.sourceforge.czt.z.ast.ImpliesPred)
     */
    @Override
    public StringBuffer visitImpliesPred(ImpliesPred pred) {
        // Implies predicates are handled by syspect and the CDD represenation of the constraint.
        throw new LocalizeException(LocalizeException.PREDICATE_TYPE_NOT_SUPPORTED
                + ImpliesPred.class
                + "\n" + pred.toString());
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.IffPredVisitor#visitIffPred(net.sourceforge.czt.z.ast.IffPred)
     */
    @Override
    public StringBuffer visitIffPred(IffPred pred) {
        // Iff predicates are handled by syspect and the CDD represenation of the constraint.
        throw new LocalizeException(LocalizeException.PREDICATE_TYPE_NOT_SUPPORTED
                + IffPred.class
                + "\n" + pred.toString());
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.MemPredVisitor#visitMemPred(net.sourceforge.czt.z.ast.MemPred)
     */
    @Override
    public StringBuffer visitMemPred(MemPred pred) {
        // 1. case: the pred is a membership predicate 
        if(!pred.getMixfix()) {
			throw new LocalizeException(LocalizeException.PREDICATE_TYPE_NOT_SUPPORTED
                + MEMBERSHIP_PREDICATE
                + "\n" + pred.toString());
		}
        
        final StringBuffer result = new StringBuffer();
        
        // 2. case: the pred is an equality predicate 
        if(pred.getRightExpr() instanceof SetExpr){
            result.append(pred.getLeftExpr().accept(this));
            result.append(LocalizeWriter.LocalizeString.EQUALS);
            final SetExpr singleton = (SetExpr) pred.getRightExpr();
            for (final Expr expr : singleton.getZExprList()) {
                result.append(expr.accept(this));
            }
        }else{
            // 3. case: the pred is a other relation
            if(pred.getRightExpr() instanceof RefExpr) {
                final OperatorName op = ((RefExpr)pred.getRightExpr()).getZName().getOperatorName();
                try {
                    // opShape reflects the shape of the operator, e.g., ["_","<","_"]
                    final StringBuilder operatorResult = new StringBuilder();
                    final StringBuilder operatorSuffix = new StringBuilder();
                    final String[] opShape = op.getWords();
                    if(!op.isUnary() && pred.getLeftExpr() instanceof TupleExpr){
                        final Iterator<Expr> tuple = ((TupleExpr)pred.getLeftExpr()).getZExprList().iterator();
                        for (int i = 0; i < opShape.length; i++) {
                            if(opShape[i].equals(ZString.ARG)) {
								operatorResult.append(tuple.next().accept(this));
							} else {
                                if(opShape[i].equals(ZString.NEQ)){
                                    result.append(LocalizeString.NOT + "(");
                                    operatorSuffix.append(")");
                                    operatorResult.append(LocalizeString.EQUALS);
                                }else{
                                    operatorResult.append(LocalizeWriter.operatorFor(opShape[i]));
                                }
                            }
                        }
                    }else{
                        for (int i = 0; i < opShape.length; i++) {
                            if(opShape[i].equals(ZString.ARG)) {
								operatorResult.append(pred.getLeftExpr().accept(this));
							} else {
                                if(opShape[i].equals(ZString.NEQ)){
                                    result.append(LocalizeString.NOT + "(");
                                    operatorSuffix.append(")");
                                    operatorResult.append(LocalizeString.EQUALS);
                                }else{
                                    operatorResult.append(LocalizeWriter.operatorFor(opShape[i]));
                                }
                            }
                        }
                    }
                    result.append(operatorResult).append(operatorSuffix);
                } catch (final NoSuchElementException e) {
                    e.printStackTrace();
                    throw new LocalizeException(LocalizeException.MALFORMED_OPERATOR_APPLICATION
                            + "\n" + op);
                }
            }else {
                throw new LocalizeException(LocalizeException.UNEXPECTED_PREDICATE
                        + "\n" + pred.getRightExpr().toString());
                
            }
            
//            removePrimesFromConstants(pred);
//            StringWriter sw = new StringWriter();
//            PrintUtils.printUnicode(pred, sw, sectionInfo, ZWrapper.getSectionName());
//           result.append(sw);
        }
        
        return result;
    }



    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ApplExprVisitor#visitApplExpr(net.sourceforge.czt.z.ast.ApplExpr)
     */
    @Override
    public StringBuffer visitApplExpr(ApplExpr appl) {
        final StringBuffer result = new StringBuffer();
        if(appl.getMixfix() && appl.getRightExpr() instanceof TupleExpr) { // Infix application of operators
            final OperatorName op = ((RefExpr)appl.getLeftExpr()).getZName().getOperatorName();
            final String[] opShape = op.getWords();
            final Iterator<Expr> tuple = ((TupleExpr)appl.getRightExpr()).getZExprList().iterator();
            for (int i = 0; i < opShape.length; i++) {
                if(opShape[i].equals(ZString.ARG)) {
                    final Expr nextExpr = tuple.next();
                    if(nextExpr instanceof ApplExpr &&
                            ((ApplExpr)nextExpr).getMixfix()) {// parantheses necessary
                        result.append(LocalizeString.LPAREN);
                        result.append(nextExpr.accept(this));
                        result.append(LocalizeString.RPAREN);
                    }else {// parantheses not necessary
                        result.append(nextExpr.accept(this));
                    }
                } else {
                    if(opShape[i].equals(LocalizeWriter.Z_DIV)) {
						result.append(LocalizeString.DIV);
					} else {
						result.append(opShape[i].trim());
					}
                }
            }
        }else{ // Prefix application of operators
            result.append(appl.getLeftExpr().accept(this));
            if(appl.getRightExpr().getAnn(ParenAnn.class) != null &&
                    appl.getRightExpr() instanceof RefExpr) {
				result.append(appl.getRightExpr().accept(this));
			} else {
				result.append(LocalizeString.LPAREN + appl.getRightExpr().accept(this) + LocalizeString.RPAREN);
			}
        }
        return result;
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.NumExprVisitor#visitNumExpr(net.sourceforge.czt.z.ast.NumExpr)
     */
    @Override
    public StringBuffer visitNumExpr(NumExpr num) {
        final StringBuffer result = new StringBuffer();
        //result.append(LocalizeString.LPAREN);
        result.append(LocalizeString.NUMPREFIX).append(num.getValue());
        //result.append(LocalizeString.RPAREN);
        return result;
    }




}
