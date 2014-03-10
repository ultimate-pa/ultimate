package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.NaiveDestructiveEqualityResolution;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;

/**
 * Provides methods to build TransitionsFormulas for the nodes and edges of a
 * recursive control flow graph.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TransFormulaBuilder {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	//We use Boogie2SMT to translate boogie Statements to SMT formulas 
	private final Boogie2SMT m_Boogie2smt;
	private final RootAnnot m_RootAnnot;
	private final boolean m_SimplifyCodeBlocks;

	public TransFormulaBuilder(Boogie2SMT boogie2smt, RootAnnot rootAnnot) {
		m_Boogie2smt = boogie2smt;
		m_RootAnnot = rootAnnot;
		m_SimplifyCodeBlocks = (new UltimatePreferenceStore(
				   RCFGBuilder.s_PLUGIN_ID)).getBoolean(PreferenceInitializer.LABEL_Simplify);
	}
	
	/**
	 * Add TransitionFormulas to an edge in the recursive control flow graph. If
	 * the edge is a CallEdge or ReturnEdge two formulas are added. One that
	 * represents the local variable assignments one that represents the global
	 * variable assignments. If the edge is an InternalEdge one 
	 * TransitionFormula is added. This TransitionFormula represents the effect
	 * of all Assignment, Assume and Havoc Statements of this edge. If the edge
	 * is a GotoEdge or a SummaryEdge no TransitionFormula is added. 
	 * @param edge An IEdge that has to be a CallEdge, InternalEdge, ReturnEdge,
	 *  GotoEdge or SummaryEdge.
	 */
	public void addTransitionFormulas(RCFGEdge edge) {
		if (edge instanceof Call || edge instanceof Return) {
			throw new AssertionError();
		} 
		else if (edge instanceof GotoEdge) {
			throw new IllegalArgumentException("Auxiliary Gotos should have" +
					"been removed.");
		}
		else if (edge instanceof Summary) {
			Summary summary = (Summary) edge;
			summary.setTransitionFormula(getTransitionFormula(summary));
		}
		else if (edge instanceof CodeBlock) { 
			StatementSequence stseq = (StatementSequence) ((RCFGEdgeAnnotation) edge
					.getPayload().getAnnotations().get(Activator.PLUGIN_ID))
					.getBackingEdge();
			stseq.setTransitionFormula(getTransitionFormula(stseq));	
		}
		else {
			throw new IllegalArgumentException();
		}
	}


//	/**
//	 * @return TransitionFormula that represents the effect of the input st.
//	 */
//	private TransFormula getTransitionFormula(AssignmentStatement st) {
//		m_Boogie2smt.startBlock();
//		m_Boogie2smt.addAssignment(st);
//		TransFormula tf = constructTransFormula();
//		m_Boogie2smt.incGeneration();
//		m_Boogie2smt.endBlock();
//		return tf;
//	}
//	
//	/**
//	 * @return TransitionFormula that represents the effect of the input st.
//	 */
//	private TransFormula getTransitionFormula(AssumeStatement st) {
//		m_Boogie2smt.startBlock();
//		m_Boogie2smt.addAssume(st);
//		TransFormula tf = constructTransFormula();
//		m_Boogie2smt.incGeneration();
//		m_Boogie2smt.endBlock();
//		return tf;
//	}
	
	
	/**
	 * @return TransitionFormula that represents the effect of the input st.
	 */
	private TransFormula getTransitionFormula(Summary summary) {
		m_Boogie2smt.startBlock();
		m_Boogie2smt.addProcedureCall(summary.getCallStatement());
		TransFormula tf = constructTransFormula(summary, m_SimplifyCodeBlocks);
		m_Boogie2smt.incGeneration();
		m_Boogie2smt.endBlock();
		return tf;
	}
	
	
	/**
	 * @param stmts List of Statements which may only be of type Assume,
	 * 	Assignment or Havoc Statement. 
	 * @return TransitionFormula that represents the effect of all input
	 *  Statements executed in a row.
	 */
	private TransFormula getTransitionFormula(StatementSequence stseq) {
		List<Statement> stmts = stseq.getStatements();
		m_Boogie2smt.startBlock();
		m_Boogie2smt.incGeneration();
		
		for (ListIterator<Statement> it = stmts.listIterator(stmts.size());
	     it.hasPrevious();) {
			Statement st = it.previous();
			if (st instanceof AssumeStatement) {
				m_Boogie2smt.addAssume((AssumeStatement) st);
			} else if (st instanceof AssignmentStatement) {
				m_Boogie2smt.addAssignment((AssignmentStatement) st);
			} else if (st instanceof HavocStatement) {
				m_Boogie2smt.addHavoc((HavocStatement) st);
			} else {
				throw new IllegalArgumentException("Intenal Edge only contains"
						+ " Assume, Assignment or Havoc Statement");
			}
		}
		TransFormula tf = constructTransFormula(stseq, m_SimplifyCodeBlocks);
		m_Boogie2smt.incGeneration();
		m_Boogie2smt.endBlock();
		return tf;
	}
	
	
	private TransFormula constructTransFormula(CodeBlock cb, boolean simplify){
		Set<TermVariable> auxVars = m_Boogie2smt.getAuxVars();
		Term formula = m_Boogie2smt.getAssumes();
		formula = eliminateAuxVars(m_Boogie2smt.getAssumes(),auxVars);

		try {
			if (simplify) {
				formula = (new SimplifyDDA(m_Boogie2smt.getScript())).
						getSimplifiedTerm(formula);
			} else {
				LBool isSat = Util.checkSat(m_Boogie2smt.getScript(), formula);
				if (isSat == LBool.UNSAT) {
					formula = m_Boogie2smt.getScript().term("false");
				}
			}
		}
		catch (SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				reportUnsupportedSyntax(cb,e.getMessage());
			}
			throw e;
		}
		Infeasibility infeasibility;
		if (formula == m_Boogie2smt.getScript().term("false")) {
			infeasibility = Infeasibility.INFEASIBLE;
		} else {
			infeasibility = Infeasibility.UNPROVEABLE;
		}
		HashMap<BoogieVar, TermVariable> inVars = m_Boogie2smt.getInVars();
		HashMap<BoogieVar, TermVariable> outVars = m_Boogie2smt.getOutVars();
		
		TransFormula.removeSuperfluousVars(formula, inVars, outVars, auxVars);
		HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, m_Boogie2smt);
		TransFormula tf = new TransFormula(formula,	inVars, outVars, auxVars, 
				branchEncoders, infeasibility, closedFormula);
		return tf;
	}
	
	
	
	/**
	 * Eliminate auxVars from input if possible. Let {x_1,...,x_n} be a subset 
	 * of auxVars. Returns a term that is equivalent to ∃x_1,...,∃x_n input and
	 * remove {x_1,...,x_n} from auxVars.
	 * The set {x_1,...,x_n} is determined by NaiveDestructiveEqualityResolution.
	 * 
	 * Returns term that is 
	 * equisatisfiable to input.  If a x is free variable 
	 * @param input
	 * @param auxVars set of free variables occurring in input
	 * @return 
	 */
	private Term eliminateAuxVars(Term input, Set<TermVariable> auxVars) {
		NaiveDestructiveEqualityResolution der = 
				new NaiveDestructiveEqualityResolution(m_Boogie2smt.getScript());
		Term result = der.eliminate(auxVars, input);
		return result;		
	}
	
	
	
	/**
	 * Returns a TransFormula that describes the assignment of arguments to
	 * callees (local) input parameters.
	 * The (local) input parameters of the callee are the only outVars. For each
	 * inParameter we construct a new BoogieVar which is equivalent to the
	 * BoogieVars which were constructed while processing the callee. 
	 */
	public TransFormula inParamAssignment(CallStatement st, Procedure callerImpl) {
		String callee = st.getMethodName();
		Map<BoogieVar,TermVariable> inVars = new HashMap<BoogieVar,TermVariable>();
		Map<BoogieVar,TermVariable> outVars = new HashMap<BoogieVar,TermVariable>();
		Set<TermVariable> allVars = new HashSet<TermVariable>();
		Term formula = m_Boogie2smt.getScript().term("true");
		Procedure calleeImpl = m_RootAnnot.getImplementations().get(callee);
//		m_Boogie2smt.declareLocals(callerImpl);
		int offset = 0;
		Term[] argTerms = m_Boogie2smt.expressions2terms(st.getArguments(), inVars, allVars);
		for (VarList varList : calleeImpl.getInParams()) {
			IType type = varList.getType().getBoogieType();
			Sort sort = m_Boogie2smt.getTypeSortTranslator().getSort(type, varList);
			for (String var : varList.getIdentifiers()) {
				BoogieVar boogieVar = m_Boogie2smt.getBoogie2SmtSymbolTable().getBoogieVar(var, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, callee), false); 
						//m_Boogie2smt.getLocalBoogieVar(callee, var);
				String varname = callee + "_" + var + "_" + "InParam";
				TermVariable tv = m_Boogie2smt.getScript().variable(varname, sort);
				outVars.put(boogieVar,tv);
				Term assignment = m_Boogie2smt.getScript().term("=", tv, argTerms[offset]);
				formula = Util.and(m_Boogie2smt.getScript(), formula, assignment);
				offset++;
			}
		}
		assert (st.getArguments().length == offset);
//		m_Boogie2smt.removeLocals(calleeImpl);
		allVars.addAll(outVars.values());
		HashSet<TermVariable> auxVars = new HashSet<TermVariable>(0);
		HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, m_Boogie2smt);
		return new TransFormula(formula, inVars, outVars, 
				auxVars, branchEncoders, 
				TransFormula.Infeasibility.UNPROVEABLE,closedFormula);
	}
	
	/**
	 * Returns a TransFormula that describes the assignment of (local) out 
	 * parameters to variables that take the result.
	 * The variables on the left hand side of the call statement are the only 
	 * outVars. For each outParameter and each left hand side of the call we
	 * construct a new BoogieVar which is equivalent to the BoogieVars of the
	 * corresponding procedures. 
	 */
	public TransFormula resultAssignment(CallStatement st, String caller) {
		String callee = st.getMethodName();
		Map<BoogieVar,TermVariable> inVars = new HashMap<BoogieVar,TermVariable>();
		Map<BoogieVar,TermVariable> outVars = new HashMap<BoogieVar,TermVariable>();
		Set<TermVariable> allVars = new HashSet<TermVariable>();
		Term formula = m_Boogie2smt.getScript().term("true");
		Procedure impl = m_RootAnnot.getImplementations().get(callee);
		int offset = 0;
		for (VarList varList : impl.getOutParams()) {
			IType type = varList.getType().getBoogieType();
			Sort sort = m_Boogie2smt.getTypeSortTranslator().getSort(type, varList);
			for (String outVar : varList.getIdentifiers()) {
				BoogieVar outBoogieVar = m_Boogie2smt.getBoogie2SmtSymbolTable().getBoogieVar(outVar, new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, callee), false); 
						//m_Boogie2smt.getLocalBoogieVar(callee, outVar); 
				String outTvName = callee + "_" + outVar + "_" + "OutParam";
				TermVariable outTv = m_Boogie2smt.getScript().variable(outTvName, sort);
				inVars.put(outBoogieVar,outTv);
				String resVar = st.getLhs()[offset].getIdentifier();
				BoogieVar resBoogieVar;
				{
					resBoogieVar = m_Boogie2smt.getBoogie2SmtSymbolTable().getBoogieVar(resVar, ((VariableLHS)st.getLhs()[offset]).getDeclarationInformation(), false); 
							//m_Boogie2smt.getLocalBoogieVar(caller, resVar);
//					if (resBoogieVar == null) {
//						// case where left hand side of call is global variable
//						resBoogieVar =  
//								//m_Boogie2smt.getGlobals().get(resVar);
//						assert resBoogieVar != null;
//					}
					assert resBoogieVar != null;
				}
				String resTvName = caller + "_" + resVar + "_" + "lhs";
				TermVariable resTv = m_Boogie2smt.getScript().variable(resTvName, sort);
				outVars.put(resBoogieVar,resTv);
				Term assignment = m_Boogie2smt.getScript().term("=", resTv, outTv);
				formula = Util.and(m_Boogie2smt.getScript(), formula, assignment);
				offset++;
			}
		}
		assert (st.getLhs().length == offset);
		allVars.addAll(inVars.values());
		allVars.addAll(outVars.values());
		HashSet<TermVariable> auxVars = new HashSet<TermVariable>(0);
		HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, m_Boogie2smt);
		return new TransFormula(formula, inVars, outVars, 
				auxVars, branchEncoders,
				TransFormula.Infeasibility.UNPROVEABLE,closedFormula);
	}
	


	void reportUnsupportedSyntax(CodeBlock cb, String longDescription) {
		ILocation loc = cb.getPayload().getLocation();
		SyntaxErrorResult result = new SyntaxErrorResult(Activator.PLUGIN_NAME,loc,longDescription);
		UltimateServices.getInstance().reportResult(Activator.PLUGIN_ID, result);
		UltimateServices.getInstance().cancelToolchain();
	}
}
