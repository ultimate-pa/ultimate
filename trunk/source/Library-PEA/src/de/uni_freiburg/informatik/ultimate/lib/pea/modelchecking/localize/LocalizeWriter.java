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

import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.ZDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.TCSWriter;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2TCSConverter.TransitionConstraint;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.TermToZCDDVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZTerm;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.z.ZWrapper;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.z.util.ZString;

/**
 * LocalizeWriter is an instance of TCSWriter. It is the writer class for PEA2TCSConverter
 * for the Localize export, that is it writes a TCS converted by PEA2TCSConverter in Localize
 * syntax into a file.
 * 
 * TODO Refactor to get a convenient structure of this class. Its quite chaotic at the moment.
 * 
 * @author jfaber
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.PEA2TCSConverter
 * @see de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.TCSWriter
 * 
 */
public class LocalizeWriter extends TCSWriter {
    
    public static class LocalizeString {
        public static final String DIV = "/";
        public static final String EQUALS = "=";
        public static final String FREETYPE = "free#";
        public static final String POINTERTYPE = "pointer#";
        public static final String GEQ = ">=";
        public static final String GREATER = ">";
        public static final String INT = "int";
        public static final String LEQ = "<=";
        public static final String LESS = "<";
        public static final String INDENT = "           ";
        public static final String LPAREN = "(";
        public static final String MINUS = "-";
        public static final String NOT = "NOT";
        public static final String AND = "AND";
        public static final String OR = "OR";
        public static final String NUMPREFIX = "_";
        public static final String PRIME = "'";
        public static final String REAL = "real";
        public static final String RPAREN = ")";
        public static final String SEPARATOR = "XXX";
        public static final String SEQUENT = " --> ";
        public static final String FORALL = "FORALL";
        public static final String NULLPOINTER = "null_";
    }
    
    public enum PC {
        NONE,
        SINGLE,
        MULTIPLE
    }
    
    private static final String FILENAME_TASK_SUFFIX = "_TASK";
    
    /**
     * Syspect operator for division.
     */
    public static final String Z_DIV = "div";

    /**
     * Syspect type name for integers.
     */
    private static final String Z_INT_TYPE = ZString.NUM;

    /**
     * Syspect type name for reals.
     */
    public static final String Z_REAL_TYPE = "\u211D";

    /**
     * If pcFlag is set to MULTIPLE, a single program counter
     * for every component is used. Otherwise, we use only one program
     * counter reflecting a compound location (SINGLE) or we export no
     * program counter at all (NONE).
     */
    private PC pcFlag = PC.NONE;
    
    /**
     * If this flag is set to false then the output localize file contains a
     * "Query" section. The user specified query is divided into a clauses part
     * containing universal quantifiers and the actual query part without quantifiers.
     * If the flag is set to true the Formulas section is used instead of the Query section.
     * In this case the user specified query is considered as invariant, i.e.,
     * it is put in the clauses section and its primed negation is put in the formulas
     * part.
     * TODO Make this decision dependent on a user decision, e.g., via checkbox
     * or preferences.
     */
    private static final boolean CHECK_QUERY_AS_INVARIANT = true;

    /**
     * A set of constant symbols that do not need to be primed.
     */
    private final Set<String> unprimedGlobalConstants = new HashSet<>();

    private int fileCounter;

    private String fileNameSuffix = ".loc";

    /**
     * Every Z free type name belongs to a localize type free#i or
     * pointer#i, where i is an integer. This map relates Z free type names to
     * this i that allow us to construct the localize type name.
     */
    private Map<String, Integer> freeTypes;
    
    /**
     * The query in localize representation.
     */
    private String localizeQuery;
    
    /**
     * The query as unicode string
     */
    private String unicodeQuery;

    /**
     * Contains all function symbols (arity 0 or higher) of the currently
     * processed model as declared
     * in the corresponding PEA and assigns this variables to their
     * localize types.
     */
    private Map<String, String> functionSymbols;
    
    /**
     * Maps function symbols to its arity.
     */
    private Map<String, Integer> arity;

    /**
     * This map contains a translation for constraints expressing that
     * function symbols (with arity > 1) are not changed, i.e. for a constraint
     *     f'=f
     * for f : \real \times \real the map provides the translation
     *     (FORALL x1,x2). f'(x1,x2)=f(x1,x2)
     */
    private Map<String, String> unchangedVarMap;

    /**
     * FileWriter to output file.
     */
    FileWriter writer;

    private CollectFunctionsVisitor queryFunctions;

    private String queryClauses;

    private String currentIndent = LocalizeString.INDENT;

    private Map<String,String> zVariables;

    /**
     * Flag that indicates that the Localize type pointer# is used instead of
     * the localize type for free types (free#).
     * 
     */
    private boolean usePointerType;
    
    /**
     * A map assigning Z variable names to their extension levels.
     */
    private Map<String, Integer> extensionLevels;

    private List<Integer> stableExts;

    /**
     * List of user specified null pointers (Z symbols).
     */
    private List<String> nullPointers;

    /**
     * Maps the user-specified
     * Z null symbols to the default localize null symbols.
     */
    private final Map<String,String> nullPointerMap;

    private final String andDelimiter = ";\n";
    
    private Set<String> pcVars;

    private ArrayList<String> pcQuery;


    /**
     * Constructor with fileName of Localize output file.
     * @param fileName
     *          output file name
     */
    public LocalizeWriter(final String fileName) {
        super(fileName);
        final int extIndex = fileName.lastIndexOf('.');
        this.fileName = fileName.substring(0, extIndex);
        fileNameSuffix = fileName.substring(extIndex);

        functionSymbols = new HashMap<>();
        arity = new HashMap<>();
        unchangedVarMap = new HashMap<>();
        fileCounter = 0;
        usePointerType = false;
        extensionLevels = new HashMap<>();
        nullPointerMap = new HashMap<>();
    }

    /**
     * @param file
     * @param extensionLevels
     * @param query
     * @param usePointerTypes
     * @param multiplePCsFlag
     */
    public LocalizeWriter(final String file, final Map<String, Integer> extensionLevels,
            final List<Integer> stableExts, final List<String> nullPointers,
            final String query, final PC pcFlag, final boolean usePointerTypes) {
        this(file);
        unicodeQuery = query.replaceAll("\n", "\n" + LocalizeString.INDENT);
        this.pcFlag = pcFlag;
        usePointerType = usePointerTypes;
        this.extensionLevels = extensionLevels;
        this.stableExts = stableExts;
        this.nullPointers = nullPointers;
    }


    /* (non-Javadoc)
     * @see pea.modelchecking.TCSWriter#write(pea.modelchecking.PEA2TCSConverter)
     */
    @Override
    public void write() {
        try {
            localizeQuery = null;
            fileCounter = 0;
            zVariables = converter.getVariables();
            // TODO jf: handle initConstraints
            final TransitionConstraint firstTrans = converter.getNextTransitionConstraint() ;
            transformTypes();
            buildNullPointerMap();
            addProgramCounter(firstTrans);
            processQuery();
            buildUnchangedVarMap();
            writeTransitions(firstTrans);

        } catch (final IOException e) {
            e.printStackTrace();
        } catch (final ParseException e) {
            e.printStackTrace();
        } catch (final InstantiationException e) {
            e.printStackTrace();
        }
    }

    /**
     * Builds a map (<code>nullPointerMap</code>) that maps the user-specified
     * Z null symbols to the default localize null symbols.
     */
    private void buildNullPointerMap() {
        if(usePointerType){
            for(final String nullPointer : nullPointers){
                final String type = zVariables.get(nullPointer).trim();
                if(type == null ||
                    freeTypes.get(type) == null) {
					throw new LocalizeException(LocalizeException.WRONG_NULLPOINTER_TYPE
                            + nullPointer);
				} else {
					nullPointerMap.put(nullPointer,LocalizeString.NULLPOINTER + freeTypes.get(type));
				}
            }
        }
    }

    /**
     * Returns the Localize representation for a given Z operator.
     * @param string
     *                  Z operator that shall be transformed
     * @return
     *                  Localize operator
     */
    public static String operatorFor(final String string) {
        if(string.equals(ZString.EQUALS)) {
			return LocalizeString.EQUALS;
		}
        if(string.equals(ZString.LESS)) {
			return LocalizeString.LESS;
		}
        if(string.equals(ZString.GREATER)) {
			return LocalizeString.GREATER;
		}
        if(string.equals(ZString.LEQ)) {
			return LocalizeString.LEQ;
		}
        if(string.equals(ZString.GEQ)) {
			return LocalizeString.GEQ;
		}

        return null;
    }
    

    /* (non-Javadoc)
     * @see pea.modelchecking.TCSWriter#writeAndDelimiter()
     */
    @Override
    protected void writeAndDelimiter(final Writer writer) throws IOException {
        writer.write(andDelimiter );
    }
    

    /* (non-Javadoc)
     * @see pea.modelchecking.TCSWriter#writeDecision(pea.Decision)
     */
    @Override
    protected void writeDecision(final Decision dec, final int child, final Writer outputWriter) throws IOException {
        writeDecision(dec, child, outputWriter, true);
    }

    /**
     * TODO: JF comment
     * @param dec
     * @param child
     * @param outputWriter
     * @throws IOException
     */
    private void writeDecision(final Decision dec, final int child, final Writer outputWriter,final boolean useClausesForm)
            throws IOException {
        //StringBuilder buf = new StringBuilder(currentIndent );
        outputWriter.append(currentIndent);
        final String andSep = ",";
        
        if(dec instanceof RangeDecision){
                final String variable = ((RangeDecision)dec).getVar();
                outputWriter.append(variable);

                final int[] limits = ((RangeDecision)dec).getLimits();
                if (child == 0) {
                        if ((limits[0] & 1) == 0) {
                                outputWriter.append(LocalizeString.LESS);
                        } else {
                                outputWriter.append(LocalizeString.LEQ);
                        }
                        outputWriter.append(LocalizeString.NUMPREFIX + (limits[0] / 2));
                        return;
                }
                if (child == limits.length) {
                        if ((limits[limits.length - 1] & 1) == 1) {
                                outputWriter.append(LocalizeString.GREATER);
                        } else {

                                outputWriter.append(LocalizeString.GEQ);
                        }
                        outputWriter.append(LocalizeString.NUMPREFIX + (limits[limits.length - 1] / 2));
                        return;
                }
                if (limits[child - 1] / 2 == limits[child] / 2) {
                        outputWriter.append(LocalizeString.GREATER);
                        outputWriter.append(LocalizeString.NUMPREFIX + (limits[child] / 2));
                        return;
                }
                if ((limits[child - 1] & 1) == 1) {
                                outputWriter.append(LocalizeString.GREATER);
                } else {
                                outputWriter.append(LocalizeString.GEQ);
            }
                outputWriter.append(LocalizeString.NUMPREFIX + (limits[child - 1] / 2));
                
                outputWriter.append(andSep).append(variable);
            
                if ((limits[child] & 1) == 0) {
                        outputWriter.append(LocalizeString.LESS);
                } else {
                        outputWriter.append(LocalizeString.LEQ);
                }
                outputWriter.append(LocalizeString.NUMPREFIX + (limits[child] / 2));
                return;
        }
        if(child==0){
                if(dec instanceof BooleanDecision){
                    final String toWrite = ((BooleanDecision)dec).getVar();
                    outputWriter.append(toWrite);
                } else if(dec instanceof EventDecision){
                        final String event = ((EventDecision)dec).getEvent();
                        outputWriter.append(event+LocalizeString.GREATER+event+"'");
                } else if (dec instanceof ZDecision) {
                    writeZDecision((ZDecision)dec, outputWriter,useClausesForm);
                }
        }else{
                if(dec instanceof BooleanDecision){
                    final String toWrite = ((BooleanDecision)dec).getVar();
                    // The following seems to implement negation of boolean
                    // expression. But only for very restrictive cases (without a check
                    // that the current instance is really of the desired shape).
                    // Not important here, because normally for Localize output no BooleanDecisions
                    // are used.
                    if(toWrite.matches("(.+)<=(.+)")){
                        outputWriter.append(toWrite.replace("<=", ">"));
                    }else if(toWrite.matches("(.+)>=(.+)")){
                        outputWriter.append(toWrite.replace(">=", "<"));
                    }else if(toWrite.matches("(.+)<(.+)")){
                        outputWriter.append(toWrite.replace("<", ">="));
                    }else if(toWrite.matches("(.+)>(.+)")){
                        outputWriter.append(toWrite.replace(">", "=<"));
                    }else{
                        outputWriter.append("NOT("+toWrite + ")");
                    }
                } else if(dec instanceof EventDecision){
                    final String event = ((EventDecision)dec).getEvent();
                    outputWriter.append(event+" = "+event+"'");
                } else if (dec instanceof ZDecision) {
                    writeZDecision(((ZDecision)dec).negate(),outputWriter,useClausesForm);
                }
        }
    }
    
    

    /**
     * Write the declarations part (which every localize file should have) for
     * the current constraint into the Localize file.
     * 
     * @param constraint
     *          the constraint that is written to file
     * @throws IOException
     *          if an exception occurs while writing the file
     * @throws InstantiationException
     *          if an uninitialized ZWrapper is used for parsing Z expression
     * @throws ParseException
     *          a parse exception thrown by the czt toolkit
     * 
     */
    protected void writeDeclarations(final TransitionConstraint constraint)
            throws IOException, ParseException, InstantiationException {
        writer.write("\n% " + converter.getName() + "\n\n");
        
        final CollectFunctionsVisitor visitor = new CollectFunctionsVisitor(functionSymbols);
        final Set<String> decisionCache = new HashSet<>();
        collectFunctionsFromCDDCached(constraint.getConstraint(),visitor,decisionCache);

        // Base functions
        writer.write("Base_functions:={");
        //this.writer.write(queryBaseFunctions);
        final Set<String> baseFun = visitor.getBaseFunctions();
        baseFun.addAll(queryFunctions.getBaseFunctions());
        for (final Iterator<String> i = baseFun.iterator() ; i.hasNext() ;) {
            writer.write("(" + replaceZSymbols(i.next()) + ", 2)");
            if(i.hasNext()) {
				writer.write(", ");
			}
        }
        writer.write("}\n");

        // Extension functions
        /* functions with arity 0 are constants for localize */
        final Map<String,String> extFun = visitor.getExtFunctions();
        writer.write("Extension_functions:={");
        extFun.putAll(queryFunctions.getExtFunctions());
        /* We collect all constant symbols (functions with arity 0) into this
         * set */
        final Set<String> constants = new HashSet<>();
        for (final Iterator<String> i = extFun.keySet().iterator(); i.hasNext() ; ) {
            final String var = i.next();
            final String varWithoutPrime = var.replaceAll(ZString.PRIME, "");
            if(arity.get(varWithoutPrime) == 0) {
                constants.add(var);
                continue;
            }
            String varName;
            Integer extLevel;
            //ignore primes from imprimedGlobalConstants
            if(var.contains(ZString.PRIME) &&
                    unprimedGlobalConstants.contains(varWithoutPrime)){
                if(extFun.keySet().contains(varWithoutPrime)) {
					continue;
				}
                extLevel = extensionLevels.get(varWithoutPrime);
                varName = replaceZSymbols(varWithoutPrime);
            }else {
                extLevel = extensionLevels.get(var);
                varName = replaceZSymbols(var);
            }
            
            if(extLevel == null) {
				throw new LocalizeException(LocalizeException.EXTENSION_LEVEL_NOT_DEFINED + var);
			}
//            if(var.contains(ZString.PRIME))
//                extLevel = 2;
//            else
//                extLevel = 1;
            //write tuple (varname,arity,level,domain,range)
            if(varName.startsWith(LocalizeString.NUMPREFIX)) {
				varName = varName.substring(1);
			}
            writer.write("(" + varName + ","
                    + arity.get(varWithoutPrime)
                    + "," + extLevel  + "," +
                    extFun.get(var) + ")");
            if(i.hasNext()) {
				writer.write(", ");
			}
        }
        writer.write("}\n");

        // Relations
        writer.write("Relations:={");
        //this.writer.write(queryRelations);
        final Set<String> rel = visitor.getRelations();
        rel.addAll(queryFunctions.getRelations());
        for (final Iterator<String> i = rel.iterator() ; i.hasNext() ;) {
            writer.write("(" + replaceZSymbols(i.next()) + ", 2)");
            if(i.hasNext()) {
				writer.write(", ");
			}
        }
        writer.write("}\n");
        
        // Constants
        writer.write("Constants:={");
        boolean first = true;
        for (final Iterator<String> i = constants.iterator(); i.hasNext() ; ) {
            final String var = i.next();
            String varName;
            final String varNameWithoutPrime = var.replace(ZString.PRIME, "");
            /* check whether var represents a null pointer and replace this to the
             * corresponding hpilot null pointer
             */
            if(nullPointerMap.containsKey(var)){
                varName = nullPointerMap.get(var);
            }else if(nullPointerMap.containsKey(varNameWithoutPrime)){
                if(constants.contains(varNameWithoutPrime)) {
					continue;
				}
                varName = nullPointerMap.get(varNameWithoutPrime);
            }else{
                //ignore primes from unprimedGlobalConstants
                if(var.contains(ZString.PRIME) &&
                        unprimedGlobalConstants.contains(varNameWithoutPrime)){
                    if(constants.contains(varNameWithoutPrime)) {
						continue;
					}
                    varName = replaceZSymbols(varNameWithoutPrime);
                }else {
                    varName = replaceZSymbols(var);
                }
                if(varName.startsWith(LocalizeString.NUMPREFIX)) {
					varName = varName.substring(1);
				}
            }
            if(!first) {
				writer.write(", ");
			} else {
				first = false;
			}
            writer.write("(" + varName + ","
                   + extFun.get(var) + ")");
        }
        // program counter to constant declaration
        if(pcFlag.equals(PC.SINGLE)) {
            final String pc1 = constraint.getSource().replaceAll(PhaseEventAutomata.TIMES,
                    LocalizeString.SEPARATOR);
            final String pc2 = constraint.getDest().replaceAll(PhaseEventAutomata.TIMES,
                    LocalizeString.SEPARATOR);
            writer.write("(" + pc1 + ", int), " +
            		"(" + pc2 + ", int)");
        }
        writer.write("}\n");
        
        if(stableExts != null && !stableExts.isEmpty()){
            writer.write("Stable:=");
            for (final Iterator<Integer> i = stableExts.iterator(); i.hasNext();) {
                writer.write(i.next().toString());
                if(i.hasNext()) {
					writer.write(",");
				}
            }
            writer.write(";\n\n");
        }
    }
    
    /**
     * Takes a clause as CDD and output the corresponding Localize representation
     * to a writer.
     * @param clause
     *          The CDD clause to be transformed
     * @param sb
     *          The writer for the localize representation
     */
    protected void writeClauseToWriter(final CDD clause, final Writer sb) {

        final ArrayList<CDD> positives = new ArrayList<>();
        final ArrayList<CDD> negatives= new ArrayList<>();
        final CDD[] disjTerm = clause.toDNF();
        try {
            currentIndent="";
            if(disjTerm.length<=1) {
                if(clause.getChilds()[0]==CDD.TRUE) {
					writeDecision(clause.getDecision(), 0, sb);
				} else {
					writeDecision(clause.getDecision(), 1, sb);
				}
                return;
            }
            for (int k = 0; k < disjTerm.length; k++) {
                if(disjTerm[k].getChilds().length<=0 ||
                        !(disjTerm[k].getDecision() instanceof ZDecision)) {
					throw new LocalizeException(LocalizeException.UNEXPECTED_TERM
                            + disjTerm[k] );
				}
                if(disjTerm[k].getChilds()[0]==CDD.TRUE) {
					positives.add(disjTerm[k]);
				} else {
					negatives.add(disjTerm[k].negate());
				}
            }
        
            for (final Iterator<CDD> iter = negatives.iterator(); iter.hasNext();) {
                final CDD cdd = iter.next();
                writeDecision(cdd.getDecision(), 0, sb);
                //ZTerm zTerm
                //    = ZWrapper.INSTANCE.predicateToTerm(((ZDecision)cdd.getDecision()).getPredicate());
                //sb.append(zTerm.getTerm().accept(zVisitor));
                if(iter.hasNext()) {
					sb.write(", ");
				}
            }
            sb.append(LocalizeString.SEQUENT);
            for (final Iterator<CDD> iter = positives.iterator(); iter.hasNext();) {
                final CDD cdd = iter.next();
                writeDecision(cdd.getDecision(), 0, sb);
                if(iter.hasNext()) {
					sb.write(", ");
				}
            }

        } catch (final IOException e) {
            e.printStackTrace();
        }finally {
            currentIndent = LocalizeString.INDENT;
        }

    }

        /**
     * Takes a clause as CDD and output the corresponding Localize representation
     * to a writer.
     * @param clause
     *          The CDD clause to be transformed
     * @param sb
     *          The writer for the localize representation
     */
    protected void writeClauseAsDisjunction(final CDD clause, final Writer sb) {

        final CDD[] disjTerm = clause.toDNF();
        try {
            currentIndent="";
            if(disjTerm.length==1) {
                if(clause.getChilds()[0]==CDD.TRUE) {
					writeDecision(clause.getDecision(), 0, sb, false);
				} else {
					writeDecision(clause.getDecision(), 1, sb, false);
				}
                return;
            }
            sb.append(LocalizeString.OR + LocalizeString.LPAREN);
            
            for (int k = 0; k < disjTerm.length; k++) {
                if(disjTerm[k].getChilds().length<=0 ||
                        !(disjTerm[k].getDecision() instanceof ZDecision)) {
					throw new LocalizeException(LocalizeException.UNEXPECTED_TERM
                            + disjTerm[k] );
				}
                if(disjTerm[k].getChilds()[0]==CDD.TRUE){
                    writeDecision(disjTerm[k].getDecision(), 0, sb, false);
                } else {
                    sb.append(LocalizeString.NOT + LocalizeString.LPAREN);
                    writeDecision(disjTerm[k].getDecision(), 0, sb, false);
                    sb.append(LocalizeString.RPAREN);
                }
                if(k+1 < disjTerm.length) {
					sb.append(", ");
				}
            }
            sb.append(LocalizeString.RPAREN);

        } catch (final IOException e) {
            e.printStackTrace();
        }finally {
            currentIndent = LocalizeString.INDENT;
        }

    }

    
    /**
     * This method collects all constant declarations from the declaration list of the current
     * converter. It fills the field constantString with the Localize output string for these
     * constants.
     * 
     * @throws InstantiationException
     *          if an uninitialized ZWrapper is used for parsing Z expression
     * @throws ParseException
     *          a parse exception thrown by the czt toolkit
     * 
     */
    @Override
    protected CDD processDeclarations(final List<String> zDeclarations,
                final Map<String, String> variables) {
        if(zDeclarations != null){
            String declarationString = "";
            for (final String decl : zDeclarations) {
                declarationString += decl + "\n";
            }
            ZTerm zTerm;
            try {
                zTerm = ZWrapper.INSTANCE.declToTerm(declarationString);

            final ProcessDeclarationsVisitor constVisitor = new ProcessDeclarationsVisitor(zTerm);
            final Map<String,String> declarations = zTerm.getTerm().accept(constVisitor);
            freeTypes = constVisitor.getFreeTypes();

            if(declarations != null &&
                    declarations.keySet() != null){
                variables.putAll(declarations);
                unprimedGlobalConstants.addAll(declarations.keySet());
            }
            return constVisitor.getInvariant();
            } catch (final ParseException e) {
                e.printStackTrace();
                throw new LocalizeException(LocalizeException.DECLARATION_ERROR + declarationString);
            } catch (final InstantiationException e) {
                e.printStackTrace();
                throw new LocalizeException(LocalizeException.DECLARATION_ERROR + declarationString);
            }
        }
        return CDD.TRUE;
    }
    
    /**
     * This methods goes through a CDD tree and collect functions from every ZDecision using
     * a CollectFunctionsVisitor.
     * 
     * @param constraint
     *          The CDD constraint that is processed.
     * @param visitor
     *          The CollectFunctionsVisitor to extract functions from the ZDecisions
     *
     * @throws InstantiationException
     *          if an uninitialized ZWrapper is used for parsing Z expression
     * @throws ParseException
     *          a parse exception thrown by the czt toolkit
     * 
     */
    @SuppressWarnings("unused")
    private void collectFunctionsFromCDD(final CDD constraint,
            final CollectFunctionsVisitor visitor) throws ParseException, InstantiationException {
        collectFunctionsFromCDDCached(constraint,visitor,null);
    }

    /**
     * This methods goes through a CDD tree and collect functions from every ZDecision using
     * a CollectFunctionsVisitor. It caches the decisions such that every decision is processed
     * only once.
     * 
     * @param constraint
     *          The CDD constraint that is processed.
     * @param visitor
     *          The CollectFunctionsVisitor to extract functions from the ZDecisions
     * @param decCache
     *          A set of constraints as Strings that are already visited. If null, then no
     *          cache is used.
     * 
     * @throws InstantiationException
     *          if an uninitialized ZWrapper is used for parsing Z expression
     * @throws ParseException
     *          a parse exception thrown by the czt toolkit
     * 
     */
    @SuppressWarnings("unchecked")
    private void collectFunctionsFromCDDCached(final CDD constraint,
            final CollectFunctionsVisitor visitor, final Set<String> decCache)
            throws ParseException, InstantiationException {
        if (constraint == CDD.TRUE || constraint == CDD.FALSE) {
			return;
		}

        if(constraint.getDecision() instanceof ZDecision){
            final ZDecision dec = ((ZDecision)constraint.getDecision());
            if(decCache == null || !decCache.contains(dec.getPredicate())) {
                final ZTerm zTerm = ZWrapper.INSTANCE.predicateToTerm(
                        dec.getPredicate());
                zTerm.getTerm().accept(visitor);
                if(decCache != null) {
					decCache.add(dec.getPredicate());
				}
            }
        }
        /* special handling of clock expressions (RangeDecision) necessary */
        if(constraint.getDecision() instanceof RangeDecision){
            final Map<String,String> symb = visitor.getExtFunctions();
            final String clock = ((RangeDecision)constraint.getDecision()).getVar();
            if(!symb.containsKey(clock)) {
				symb.put(clock, LocalizeString.REAL);
			}
        }
        
        for (int i = 0; i < constraint.getChilds().length; i++) {
            if(constraint.getChilds()[i] == CDD.FALSE || constraint.getChilds()[i] == CDD.TRUE) {
				continue;
			}
            collectFunctionsFromCDDCached(constraint.getChilds()[i],visitor,decCache);
        }
        
    }

    
    /**
     * A simple replacement function that replaces ZString by its Localize representations.
     * @param str
     *          The string that has to be translated into Localize output.
     * @return
     *          The string after the replacement.
     */
    private String replaceZSymbols(String str) {
    //    str = str.replaceAll("(\\d+)","_$1");
        str = str.replaceAll(ZString.PRIME, LocalizeString.PRIME);
        str = str.replace(ZString.MINUS, LocalizeString.MINUS);
        str = str.replace(LocalizeWriter.Z_DIV, LocalizeString.DIV);
        str = str.replace(ZString.AND, ", ");
        return str;
    }

    
    /**
     * This method takes a list of variables with their types from the PEA2TCSConverter
     * belonging to this instance of LocalizeWriter and computes
     *          1. A free type for every basic type of the spec
     *             named by LocalizeString.FREE_TYPE + Number
     *          2. The map variables assigning variable names to their Localize type representation, ie.
     *             domain,range
     *          3. The map arity assigning variable names to their function arity
     * 
     * @throws InstantiationException
     * @throws ParseException
     */
    private void transformTypes() throws ParseException, InstantiationException {
        functionSymbols = new HashMap<>();
        arity = new HashMap<>();
      
        
        for (final String var : zVariables.keySet()) {
            //The type of var as an array with the shape [domain,range]
            final String[] type = zVariables.get(var).split(ZString.FUN);
            if(type.length == 0) {
				throw new LocalizeException(LocalizeException.TYPE_NOT_SUPPORTED + zVariables.get(var));
			}
            final String[] domains = type[0].split(ZString.CROSS);
            if(domains.length == 0) {
				throw new LocalizeException(LocalizeException.TYPE_NOT_SUPPORTED + zVariables.get(var));
			}
            final String domain = domains[0].trim();
            //very simple consistency check
            if(!Pattern.matches("[a-zA-Z_0-9\u2124\u211D]*", domain)) {
				throw new LocalizeException(LocalizeException.TYPE_NOT_SUPPORTED + zVariables.get(var));
			}
            int arityCounter;
            for (arityCounter = 1; arityCounter < domains.length; arityCounter++) {
                if(!domains[arityCounter].equals(domain)) {
					throw new LocalizeException(LocalizeException.TYPE_NOT_SUPPORTED + zVariables.get(var));
				}
            }
            String range = "";
            if(type.length > 1) { // type has a range
                range = type[1].trim();
                if(!Pattern.matches("[a-zA-Z_0-9\u2124\u211D]*", range)) {
					throw new LocalizeException(LocalizeException.TYPE_NOT_SUPPORTED + zVariables.get(var));
				}
            }
            
            //we check if the types are declared
            if(!domain.equals(Z_REAL_TYPE) && !domain.equals(Z_INT_TYPE)) {
                if(!freeTypes.containsKey(domain)) {
					throw new LocalizeException(LocalizeException.TYPE_NOT_DECLARED + domain);
				}
            }
            if(!range.equals("") && !range.equals(Z_REAL_TYPE) && !range.equals(Z_INT_TYPE)) {
                if(!freeTypes.containsKey(range)) {
					throw new LocalizeException(LocalizeException.TYPE_NOT_DECLARED + range);
				}
            }

            //we now translate the types to the Localize representations
            String locDomain;
            if(domain.equals(Z_REAL_TYPE)) {
				locDomain = LocalizeString.REAL;
			} else if(domain.equals(Z_INT_TYPE)) {
				locDomain = LocalizeString.INT;
			} else if(freeTypes.containsKey(domain)) {
				locDomain = usePointerType ?
                    LocalizeString.POINTERTYPE + freeTypes.get(domain):
                    LocalizeString.FREETYPE + freeTypes.get(domain);
			} else {
				throw new LocalizeException(LocalizeException.TYPE_NOT_SUPPORTED + domain);
			}
            
            //basing on the previous results we now compute the localize type
            String locRange;
            if(!range.equals("")) {
                if(range.equals(Z_REAL_TYPE)) {
					locRange = LocalizeString.REAL;
				} else if(range.equals(Z_INT_TYPE)) {
					locRange = LocalizeString.INT;
				} else if(freeTypes.containsKey(range)) {
					locRange = usePointerType ?
                            LocalizeString.POINTERTYPE + freeTypes.get(range):
                            LocalizeString.FREETYPE + freeTypes.get(range);
				} else {
					throw new LocalizeException(LocalizeException.TYPE_NOT_SUPPORTED + range);
				}

                //variables.put(var,arityCounter + "," + extLevel + "," + locDomain + "," + locRange);
                functionSymbols.put(var,locDomain + "," + locRange);
                arity.put(var,arityCounter);
            }else {
                functionSymbols.put(var,locDomain);
                arity.put(var,0);
            }
            
        }
        
    }


    /**
     * Add program counter of type int to function symbols depending on the
     * the current seleceted type of program counter (pcFlag).
     * @param trans
     *          an arbitrary transition constraint,
     *          it is needed to calculate the number of parallel components
     * @see pcFlag
     */
    private void addProgramCounter(final TransitionConstraint trans) {
        if(pcFlag.equals(PC.SINGLE)){
            functionSymbols.put("pc",LocalizeString.INT);
            arity.put("pc", 0);
            functionSymbols.put("pc"+ZString.PRIME,LocalizeString.INT);
            arity.put("pc" + ZString.PRIME, 0);
        }else if(pcFlag.equals(PC.MULTIPLE)) {

            pcVars = new HashSet<>();
            int numberOfComponents = 0;
            final Phase[] phases = converter.getPEA().getPhases();
            for(int i = 0; i < phases.length; i++){
                final String[] pcNames = phases[i].getName().split(PhaseEventAutomata.TIMES);
                if(numberOfComponents == 0) {
					numberOfComponents = pcNames.length;
				} else if(pcNames.length != numberOfComponents) {
					throw new LocalizeException(LocalizeException.MALFORMED_LOCATION
                            + phases[i].getName());
				}
                for (int j = 0; j < pcNames.length; j++) {
                    if(!pcVars.contains(pcNames[j])){
                        pcVars.add(pcNames[j]);
                        functionSymbols.put(pcNames[j],LocalizeString.INT);
                        unprimedGlobalConstants.add(pcNames[j]);
                        arity.put(pcNames[j], 0);
                    }
                }
            }
            
            for (int i = 0; i < numberOfComponents; i++) {
                functionSymbols.put("pc"+i,LocalizeString.INT);
                arity.put("pc" + i, 0);
                functionSymbols.put("pc"+i+ZString.PRIME,LocalizeString.INT);
                arity.put("pc" + i + ZString.PRIME, 0);
            }
        }
    }

    /**
     * Writes a single transition constraint to the output file.
     * @param constraint
     *          the constraint that has to be written into the output file
     * @throws IOException
     *          if an exception occurs while writing the file
     */
    private void writeClausesToFile(final TransitionConstraint constraint)
    throws IOException {

            writer.write("Clauses :=\n");
            writeConjunction(constraint.getConstraint(),writer);
            writer.write(queryClauses);
            writer.write("\n");
            
    }


    /**
     * Writes a query for the current transition constraint to the output file.
     * @throws IOException
     */
    private void writeQuery() throws IOException {
        try {
            if(localizeQuery == null) {
                processQuery();
            }
            if(CHECK_QUERY_AS_INVARIANT) {
				writer.write("Formulas :=\n");
			} else {
				writer.write("Query :=\n");
			}
            writer.write(localizeQuery);
            writer.write("\n");
            writer.write("\n");
        } catch (final ParseException e) {
            e.printStackTrace();
        } catch (final InstantiationException e) {
            e.printStackTrace();
        }
        
    }

    /**
     * Computes the localize query string from a Z query. The
     * resulting query string is stored in localizeQuery. Additionally
     * the query may contain quantified parts that cannot occur in
     * localize query expressions. So, we put this clauses part in field
     * queryClauses.
     * 
     * @throws IOException
     *          if an exception occurs while writing to the writer stream
     * @throws InstantiationException
     *          if an uninitialized ZWrapper is used for parsing Z expression
     * @throws ParseException
     *          a parse exception thrown by the czt toolkit
     */
    private void processGeneralQuery() throws ParseException, InstantiationException,
            IOException {
        final ZTerm queryTerm = ZWrapper.INSTANCE.predicateToTerm(unicodeQuery);
        
        // Generate query string
        final TermToZCDDVisitor visitor = new TermToZCDDVisitor(queryTerm);
        final CDD queryCDD = queryTerm.getTerm().accept(visitor);
        
        //separate quantified expressions from non-quantified expressions
        //a query is a conjunction term, so we use toCNF to get all of
        //its conjuncts.
        final StringWriter queryPart = new StringWriter();
        final StringWriter clausesPart = new StringWriter();

        final CDD[] conjuncts = queryCDD.toCNF();
        for (int i = 0; i < conjuncts.length; i++) {
            if(conjuncts[i].getDecision() instanceof ZDecision) {
                // just some simple string processing here to avoid
                // expensive parsing of the unicode Z expression.
                final String pred = ((ZDecision) conjuncts[i].getDecision())
                                    .getPredicate();
                if(pred.trim().startsWith(ZString.ALL)) {
                    clausesPart.write(LocalizeString.INDENT);
                    writeZDecision((ZDecision)conjuncts[i].getDecision(),clausesPart,true);
                    clausesPart.write(";\n");
                    continue;
                }
            }
            queryPart.write(LocalizeString.INDENT);
            writeClauseToWriter(conjuncts[i],queryPart);
            queryPart.write(";\n");
        }
        localizeQuery = queryPart.toString();
        queryClauses = clausesPart.toString();
        
        // Collect functions from query
        queryFunctions = new CollectFunctionsVisitor(functionSymbols);
        final Set<String> decisionCache = new HashSet<>();
        collectFunctionsFromCDDCached(queryCDD,queryFunctions,decisionCache);

        // For PC.MULTIPLE mode, we collect all relevant program counters
//        for(queryFunctions.getExtFunctions().
    }

    
    /**
     * Computes the localize query string from a Z query.
     * 
     * @throws IOException
     *          if an exception occurs while writing to the writer stream
     * @throws InstantiationException
     *          if an uninitialized ZWrapper is used for parsing Z expression
     * @throws ParseException
     *          a parse exception thrown by the czt toolkit
     */
    private void processQuery() throws ParseException, InstantiationException,
    IOException {
        
        if(CHECK_QUERY_AS_INVARIANT) {
			processInvariantQuery();
		} else {
			processGeneralQuery();
		}
        
    }

    /**
     * Computes the localize query string from a Z query.
     * Here, the query is considered to be an invariant. The user is not
     * required to manually formulate the invariant as localize query, which is
     * done automatically in this method. That is, for an invariant
     * inv the output inv AND NOT(inv') is produced, where the first part is output
     * into the Query section and the latter is output into the Formulas section.
     * 
     * @throws IOException
     *          if an exception occurs while writing to the writer stream
     * @throws InstantiationException
     *          if an uninitialized ZWrapper is used for parsing Z expression
     * @throws ParseException
     *          a parse exception thrown by the czt toolkit
     */
    private void processInvariantQuery() throws ParseException,
            InstantiationException, IOException {
        final ZTerm queryTerm = ZWrapper.INSTANCE.predicateToTerm(unicodeQuery);

        final TermToZCDDVisitor visitor = new TermToZCDDVisitor(queryTerm);
        final CDD queryCDD = queryTerm.getTerm().accept(visitor);
        
        final StringWriter queryPart = new StringWriter();
        final StringWriter formulasPart = new StringWriter();

        writeConjunction(queryCDD, queryPart);

        // to write disjunctions.
//        andDelimiter = ",\n";
//        formulasPart.append(LocalizeString.INDENT +
//                LocalizeString.NOT + LocalizeString.LPAREN + "\n");
//        formulasPart.append(LocalizeString.INDENT +
//                LocalizeString.AND  + LocalizeString.LPAREN + "\n");
//        writeConjunction(queryCDD.prime(), formulasPart);
//        formulasPart.append(LocalizeString.INDENT +
//                LocalizeString.RPAREN + LocalizeString.RPAREN + ";");
//        andDelimiter = ";\n";

        final CDD negQueryCDD = queryCDD.prime().negate();

        final CDD[] cnf = negQueryCDD.toCNF();
        
        for(int i = 0; i<cnf.length;i++){
            formulasPart.append(LocalizeString.INDENT);
            writeClauseAsDisjunction(cnf[i], formulasPart);
            formulasPart.append(andDelimiter+"\n");
        }
        
        

        queryClauses = "\n" + LocalizeString.INDENT +
            "% Invariant\n" + queryPart.toString();
        localizeQuery = formulasPart.toString();

        // Collect functions from query
        queryFunctions = new CollectFunctionsVisitor(functionSymbols);
        final Set<String> decisionCache = new HashSet<>();
        collectFunctionsFromCDDCached(negQueryCDD,queryFunctions,decisionCache);
        collectFunctionsFromCDDCached(queryCDD,queryFunctions,decisionCache);
        
        // Collect program counters from query
        if(pcFlag.equals(PC.MULTIPLE)){
            pcQuery = new ArrayList<>();
            for(final String symb : queryFunctions.getExtFunctions().keySet()){
                if(pcVars.contains(symb)) {
					pcQuery.add(symb);
				}
            }
        }
    }

    
    
    /**
     * Writes all transitions fetched from PEA2TCSConverter to the output file.
     * 
     * @param constraint
     *          The first constraint to start with.
     * @throws IOException
     *          if an exception occurs while writing the file
     * @throws InstantiationException
     *          if an uninitialized ZWrapper is used for parsing Z expression
     * @throws ParseException
     *          a parse exception thrown by the czt toolkit
     * 
     */
    private void writeTransitions(TransitionConstraint constraint) throws IOException, ParseException, InstantiationException {
        while(constraint != null) {
            writer = new FileWriter(fileName + FILENAME_TASK_SUFFIX + fileCounter++ + fileNameSuffix);
            final TransitionConstraint constraintWithPC = addPC2Constraint(constraint);
            /* write declarations, clauses, and query for one transition */
            writeDeclarations(constraintWithPC);
            writeClausesToFile(constraintWithPC);
            writeQuery();
            writer.flush();
            writer.close();
            constraint = converter.getNextTransitionConstraint() ;
        }
    }

    /**
     * @param constraint
     * @return
     */
    private TransitionConstraint addPC2Constraint(final TransitionConstraint constraint) {
     
        if(constraint.getSource().contains(LocalizeString.SEPARATOR)) {
			throw new LocalizeException(LocalizeException.MALFORMED_NAME
                    + constraint.getSource());
		}
        if(constraint.getDest().contains(LocalizeString.SEPARATOR)) {
			throw new LocalizeException(LocalizeException.MALFORMED_NAME
                    + constraint.getDest());
		}
        
        CDD newCDD = constraint.getConstraint();
        if(pcFlag.equals(PC.SINGLE)) {
            final String pc1 = constraint.getSource().replaceAll(PhaseEventAutomata.TIMES,
                    LocalizeString.SEPARATOR);
            final String pc2 = constraint.getDest().replaceAll(PhaseEventAutomata.TIMES,
                    LocalizeString.SEPARATOR);
            if(pc1.contains(LocalizeString.NUMPREFIX)) {
				throw new LocalizeException(LocalizeException.MALFORMED_NAME
                        + constraint.getSource());
			}
            if(pc2.contains(LocalizeString.NUMPREFIX)) {
				throw new LocalizeException(LocalizeException.MALFORMED_NAME
                        + constraint.getDest());
			}

            newCDD = newCDD.and(ZDecision.create("pc" + ZString.EQUALS +pc1 ));
            newCDD = newCDD.and(ZDecision.create("pc" + ZString.PRIME + ZString.EQUALS + pc2 ));

        }else if(pcFlag.equals(PC.MULTIPLE)) {

            final String[] sourcePLs =
                constraint.getSource().split(PhaseEventAutomata.TIMES);
            final String[] targetPLs =
                constraint.getDest().split(PhaseEventAutomata.TIMES);
            if(sourcePLs.length != targetPLs.length) {
				throw new LocalizeException(LocalizeException.MALFORMED_LOCATION
                        + constraint.getSource() + " or " + constraint.getDest());
			}
            for (int i = 0; i < targetPLs.length; i++) {
                
                if(sourcePLs[i].contains(LocalizeString.NUMPREFIX)) {
					throw new LocalizeException(LocalizeException.MALFORMED_NAME
                            + constraint.getSource());
				}
                if(targetPLs[i].contains(LocalizeString.NUMPREFIX)) {
					throw new LocalizeException(LocalizeException.MALFORMED_NAME
                            + constraint.getDest());
				}

                final String pc1 = "pc" + i;
                final String pc2 = "pc" + i + ZString.PRIME;
                if(queryFunctions.getExtFunctions().containsKey(pc1)) {
                    newCDD = newCDD.and(ZDecision.create(pc1 + ZString.EQUALS + sourcePLs[i] ));
                    for(final String pcName : pcQuery){
                        if(!pcName.equals(sourcePLs[i])){
                            newCDD = newCDD.and(ZDecision.create(pcName + ZString.EQUALS + sourcePLs[i] ).negate());
                        }
                    }
                }
                if(queryFunctions.getExtFunctions().containsKey(pc2)) {
                    newCDD = newCDD.and(ZDecision.create(pc2 + ZString.EQUALS + targetPLs[i] ));
                    for(final String pcName : pcQuery){
                        if(!pcName.equals(targetPLs[i])){
                            newCDD = newCDD.and(ZDecision.create(pcName + ZString.EQUALS + targetPLs[i] ).negate());
                        }
                    }
                }
            }
        }else if(pcFlag.equals(PC.NONE)){
            return constraint;
        }
        return new TransitionConstraint(newCDD,constraint.getSource(),constraint.getDest());
    }

    /**
     * Writes a ZDecision to a StringBuilder object using the LocalizeZVisitor.
     * 
     * @param dec
     *          The dec that has to be written.
     * @param useClausesForm
     * @param buf
     *          The target buffer that is filled with the textual representation of the decision
     */
    private void writeZDecision(final ZDecision dec, final Writer outputWriter, final boolean useClausesForm) {
        try {
            final ZTerm zTerm = ZWrapper.INSTANCE.predicateToTerm(dec.getPredicate());
            final LocalizeZVisitor visitor = new LocalizeZVisitor(
                    zTerm,
                    unprimedGlobalConstants,
                    functionSymbols,
                    freeTypes,
                    nullPointerMap,
                    this,useClausesForm);
            final String toWrite = replaceZSymbols(
                    zTerm.getTerm().accept(visitor).toString());
            /* We still have to transform constraints like x'=x for
               complexer types into FORALL expressions. */
            if(unchangedVarMap.containsKey(toWrite)) {
				outputWriter.write(unchangedVarMap.get(toWrite));
			} else {
				outputWriter.write(toWrite);
			}
        } catch (final ParseException e) {
            e.printStackTrace();
        } catch (final InstantiationException e) {
            e.printStackTrace();
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }
    
    /**
     * Constructs the unchangedVarMap. See comment of
     * <code>unchangedVarMap</code> for an explanation.
     */
    private void buildUnchangedVarMap() {
        unchangedVarMap = new HashMap<>();
        for(final String symb : functionSymbols.keySet()) {
            if(!arity.containsKey(symb)) {
				throw new LocalizeException(LocalizeException.TYPE_NOT_DECLARED + symb);
			}
            final int sarity = arity.get(symb);
            if(sarity>0) {
                final String left = symb + LocalizeString.PRIME + LocalizeString.EQUALS
                    + symb;
                String right =
                    LocalizeString.LPAREN +
                    LocalizeString.FORALL;
                String params = LocalizeString.LPAREN;
                for (int i = 0; i < sarity; ) {
                    right += " x" + i;
                    params += "x" + i;
                    if(++i < sarity) {
                        right += ",";
                        params += ",";
                    }else {
                        right += LocalizeString.RPAREN + ". ";
                        params += LocalizeString.RPAREN;
                    }
                }
                right += symb + LocalizeString.PRIME + params
                    + LocalizeString.EQUALS
                    + symb + params;
                unchangedVarMap.put(left, right);
            }
        }
    }



}
