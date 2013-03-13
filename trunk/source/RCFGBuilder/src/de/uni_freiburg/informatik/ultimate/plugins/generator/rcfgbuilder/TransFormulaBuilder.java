package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.NaiveDestructiveEqualityResolution;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

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

	public TransFormulaBuilder(Boogie2SMT boogie2smt, RootAnnot rootAnnot) {
		m_Boogie2smt = boogie2smt;
		m_RootAnnot = rootAnnot;
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
			if (!summary.calledProcedureHasImplementation()) {
				summary.setTransitionFormula(getTransitionFormula(summary));
			}
			else {
				//TODO
			}
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
		TransFormula tf = constructTransFormula(summary, m_RootAnnot.getTaPrefs().SimplifyCodeBlocks());
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
		TransFormula tf = constructTransFormula(stseq, m_RootAnnot.getTaPrefs().SimplifyCodeBlocks());
		m_Boogie2smt.incGeneration();
		m_Boogie2smt.endBlock();
		return tf;
	}
	
	
	private TransFormula constructTransFormula(CodeBlock cb, boolean simplify){
		Set<TermVariable> auxVars = m_Boogie2smt.getAuxVars();
		Term formula = m_Boogie2smt.getAssumes();
		formula = eliminateAuxVars(m_Boogie2smt.getAssumes(),auxVars);
		if (simplify) {
			try {
				formula = (new SimplifyDDA(m_Boogie2smt.getScript(), s_Logger)).
						getSimplifiedTerm(formula);
			}
			catch (SMTLIBException e) {
				if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
					reportUnsupportedSyntax(cb, new BoogieLocation("",0,0,0,0, false),e.getMessage());
				}
				throw e;
			}
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
		m_Boogie2smt.declareLocals(callerImpl);
		int offset = 0;
		Term[] argTerms = m_Boogie2smt.expressions2terms(st.getArguments(), inVars, allVars);
		for (VarList varList : calleeImpl.getInParams()) {
			IType type = varList.getType().getBoogieType();
			Sort sort = m_Boogie2smt.getSmt2Boogie().getSort(type, varList);
			for (String var : varList.getIdentifiers()) {
				BoogieVar boogieVar = m_Boogie2smt.getLocalBoogieVar(callee, var);
				String varname = callee + "_" + var + "_" + "InParam";
				TermVariable tv = m_Boogie2smt.getScript().variable(varname, sort);
				outVars.put(boogieVar,tv);
				Term assignment = m_Boogie2smt.getScript().term("=", tv, argTerms[offset]);
				formula = Util.and(m_Boogie2smt.getScript(), formula, assignment);
				offset++;
			}
		}
		assert (st.getArguments().length == offset);
		m_Boogie2smt.removeLocals(calleeImpl);
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
			Sort sort = m_Boogie2smt.getSmt2Boogie().getSort(type, varList);
			for (String outVar : varList.getIdentifiers()) {
				BoogieVar outBoogieVar = m_Boogie2smt.getLocalBoogieVar(callee, outVar); 
				String outTvName = callee + "_" + outVar + "_" + "OutParam";
				TermVariable outTv = m_Boogie2smt.getScript().variable(outTvName, sort);
				inVars.put(outBoogieVar,outTv);
				String resVar = st.getLhs()[offset];
				BoogieVar resBoogieVar;
				{
					resBoogieVar = m_Boogie2smt.getLocalBoogieVar(caller, resVar);
					if (resBoogieVar == null) {
						// case where left hand side of call is global variable
						resBoogieVar = m_Boogie2smt.getSmt2Boogie().getGlobals().get(resVar);
						assert resBoogieVar != null;
					}
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
	
	/**
	 * Construct auxilliary assignment of global vars needed by our 
	 * implementation trace abstraction.
	 * Return an array of two TransFormulas, for a procedure call st.
	 * For each global variable g which is modified by the called procedure
	 * <ul>
	 *  <li> the first TransFormula assigns to old(g) the value of g
	 *  <li> the second TransFormula assigns to g the value of old(g)
	 * </ul>
	 */
	public TransFormula[] globalVarAssignments(CallStatement st) {
		Map<String, ASTType> vars = m_RootAnnot.getModifiedVars().get(st.getMethodName());
		if (vars == null) {
			//no global var modified
			vars = new HashMap<String, ASTType>(0);
		}

		Map<BoogieVar,TermVariable> glob2oldInVars = new HashMap<BoogieVar,TermVariable>();
		Map<BoogieVar,TermVariable> glob2oldOutVars = new HashMap<BoogieVar,TermVariable>();
		Set<TermVariable> glob2oldAllVars = new HashSet<TermVariable>();
		Term glob2oldFormula = m_Boogie2smt.getScript().term("true");
		
		Map<BoogieVar,TermVariable> old2globInVars = new HashMap<BoogieVar,TermVariable>();
		Map<BoogieVar,TermVariable> old2globOutVars = new HashMap<BoogieVar,TermVariable>();
		Set<TermVariable> old2globAllVars = new HashSet<TermVariable>();
		Term old2globFormula = m_Boogie2smt.getScript().term("true");
		
		Map<String, BoogieVar> globals = m_Boogie2smt.getSmt2Boogie().getGlobals();
		for (String modVar : vars.keySet()) {
			BoogieVar boogieVar = globals.get(modVar);
			BoogieVar boogieOldVar = m_Boogie2smt.getSmt2Boogie().getOldGlobals().get(boogieVar.getIdentifier());
			Sort sort = m_Boogie2smt.getSmt2Boogie().getSort(boogieVar.getIType(), st);
			{
				String nameIn = modVar + "_In";
				TermVariable tvIn = m_Boogie2smt.getScript().variable(nameIn, sort);
				String nameOut = "old(" + modVar + ")" + "_Out";
				TermVariable tvOut = m_Boogie2smt.getScript().variable(nameOut, sort);
				glob2oldInVars.put(boogieVar, tvIn);
				glob2oldOutVars.put(boogieOldVar, tvOut);
				glob2oldAllVars.add(tvIn);
				glob2oldAllVars.add(tvOut);
				Term assignment = m_Boogie2smt.getScript().term("=", tvOut, tvIn);
				glob2oldFormula = Util.and(m_Boogie2smt.getScript(), glob2oldFormula, assignment);
			}
			{
				String nameIn = "old(" + modVar + ")" + "_In";
				TermVariable tvIn = m_Boogie2smt.getScript().variable(nameIn, sort);
				String nameOut = modVar + "_Out";
				TermVariable tvOut = m_Boogie2smt.getScript().variable(nameOut, sort);
				old2globInVars.put(boogieOldVar, tvIn);
				old2globOutVars.put(boogieVar, tvOut);
				old2globAllVars.add(tvIn);
				old2globAllVars.add(tvOut);
				Term assignment = m_Boogie2smt.getScript().term("=", tvOut, tvIn);
				old2globFormula = Util.and(m_Boogie2smt.getScript(), old2globFormula, assignment);
			}			
		}
		TransFormula[] result = new TransFormula[2];
		{
			HashSet<TermVariable> auxVars = new HashSet<TermVariable>(0);
			HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
			Term closedFormula = TransFormula.computeClosedFormula(
					glob2oldFormula, glob2oldInVars, glob2oldOutVars, auxVars, m_Boogie2smt);
			result[0] = new TransFormula(glob2oldFormula, glob2oldInVars,glob2oldOutVars,
					auxVars, branchEncoders,
					TransFormula.Infeasibility.UNPROVEABLE, closedFormula);
		}
		
		{
			HashSet<TermVariable> auxVars = new HashSet<TermVariable>(0);
			HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
			Term closedFormula = TransFormula.computeClosedFormula(
					old2globFormula, old2globInVars, old2globOutVars, auxVars, m_Boogie2smt);
			result[1] = new TransFormula(old2globFormula, old2globInVars, old2globOutVars,
				auxVars, branchEncoders,
				TransFormula.Infeasibility.UNPROVEABLE,closedFormula);
		}
		return result;
	}
	

	
	void reportUnsupportedSyntax(CodeBlock cb, ILocation loc, String longDescription) {
		SyntaxErrorResult result = new SyntaxErrorResult(cb,
				Activator.PLUGIN_NAME,
				UltimateServices.getInstance().getTranslatorSequence(),
				loc, SyntaxErrorType.UnsupportedSyntax);
		result.setLongDescription(longDescription);
		UltimateServices.getInstance().reportResult(Activator.PLUGIN_ID, result);
		UltimateServices.getInstance().cancelToolchain();
	}
}
