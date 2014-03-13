package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.NaiveDestructiveEqualityResolution;

public class Statements2TransFormula {
	private Script m_Script;
	
	private final String m_CurrentProcedure;
	
	private final Boogie2SmtSymbolTable m_Boogie2SmtSymbolTable;
	
	private final VariableManager m_VariableManager;
	
	private final HashSet<TermVariable> allVars;
	private final HashMap<BoogieVar, TermVariable> outVars;
	private final HashMap<BoogieVar, TermVariable> inVars;
	
	private final Boogie2SMT m_Boogie2SMT;
	private final TypeSortTranslator m_TypeSortTranslator;
	private final BoogieDeclarations m_BoogieDeclarations;

	/**
	 * Auxilliary variables. TermVariables that occur neither as inVar nor as
	 * outVar. If you use the assumes or asserts to encode a transition the
	 * auxilliary variables are existentially quantified.
	 */
	private HashSet<TermVariable> auxVars;


	
	/**
	 * True if we are translation a requires clause of the specification. In
	 * this case, a global variable g refers to the instance of the variable
	 * before the procedure call (the same instance as old(g)).
	 */
	private boolean m_TranslatingRequires = false;
	
	private Term assumes;
	private Term asserts;

//	private int m_freshConstantCounter = 0;
	
	
	public Statements2TransFormula(String currentProcedure,
			Boogie2SMT boogie2smt) {
		super();
		m_CurrentProcedure = currentProcedure;
		m_Boogie2SMT = boogie2smt;
		m_Script = boogie2smt.getScript();
		m_Boogie2SmtSymbolTable = m_Boogie2SMT.getBoogie2SmtSymbolTable();
		m_VariableManager = m_Boogie2SMT.getVariableManager();
		m_TypeSortTranslator = m_Boogie2SMT.getTypeSortTranslator();
		m_BoogieDeclarations = m_Boogie2SMT.getBoogieDeclarations();
		
		outVars = new HashMap<BoogieVar, TermVariable>();
		inVars = new HashMap<BoogieVar, TermVariable>();
		allVars = new HashSet<TermVariable>();
		auxVars = new HashSet<TermVariable>();
		assumes = m_Script.term("true");
		asserts = m_Script.term("true");
	}

	private BoogieVar getModifiableBoogieVar(String id, DeclarationInformation declInfo) {
		StorageClass storageClass = declInfo.getStorageClass();
//		assert (declInfo.getProcedure() == null || declInfo.getProcedure().equals(m_CurrentProcedure));
		BoogieVar result;
		switch (storageClass) {
		case GLOBAL:
			result = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, false);
			break;
		case LOCAL:
			result = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, false);
			break;
		case IMPLEMENTATION_OUTPARAM:
			result = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, false);
			break;
		case IMPLEMENTATION_INPARAM:
		case PROCEDURE_INPARAM:
		case PROCEDURE_OUTPARAM:
			throw new AssertionError("not modifiable");
		case IMPLEMENTATION:
		case PROCEDURE:
		case QUANTIFIED:
		default:
			throw new AssertionError("no appropriate variable ");
		}
		return result;
	}
	
	private IdentifierTranslator[] getIdentifierTranslatorsIntraprocedural() {
		return new IdentifierTranslator[] { 
				new LocalVarTranslatorWithInOutVarManagement(),
				new GlobalVarTranslatorWithInOutVarManagement(m_CurrentProcedure, false),
				m_Boogie2SMT.getConstOnlyIdentifierTranslator() 
				};
	}

	/**
	 * Let assign be a statement of the form v_i:=expr_i Remove v_i from the
	 * inVars (if contained). If neccessary v_i is put to outVars (possibly by
	 * getSmtIdentifier).
	 */
	public void addAssignment(AssignmentStatement assign) {
		LeftHandSide[] lhs = assign.getLhs();
		Expression[] rhs = assign.getRhs();
		Map<TermVariable, Expression> addedEqualities = new HashMap<TermVariable, Expression>();
		for (int i = 0; i < lhs.length; i++) {
			/* ArrayLHS are removed by preprocessor */
			VariableLHS vlhs = (VariableLHS) lhs[i];
			assert vlhs.getDeclarationInformation() != null : " no declaration information";
			String name = vlhs.getIdentifier();
			DeclarationInformation declInfo = vlhs.getDeclarationInformation();
			BoogieVar boogieVar = getModifiableBoogieVar(name, declInfo);
			assert (boogieVar != null);
			getOrConstuctCurrentRepresentative(boogieVar);
//			if (!inVars.containsKey(boogieVar)) {
//				if (!outVars.containsKey(boogieVar)) {
//					TermVariable tv = createInVar(boogieVar);
//					outVars.put(boogieVar, tv);
//				}
//			}
			if (inVars.containsKey(boogieVar)) {
				TermVariable tv = inVars.get(boogieVar);
				addedEqualities.put(tv, rhs[i]);
				removeInVar(boogieVar);
			}
		}
		IdentifierTranslator[] its = getIdentifierTranslatorsIntraprocedural();
				
		for (TermVariable tv : addedEqualities.keySet()) {
			
			Term rhsTerm = (new Expression2Term( its, m_Script, m_TypeSortTranslator, addedEqualities.get(tv))).getTerm();
			Term eq = m_Script.term("=", tv, rhsTerm);

			assumes = Util.and(m_Script, eq, assumes);
			asserts = Util.implies(m_Script, eq, asserts);
			assert (assumes.toString() instanceof Object);
		}
	}

	public void addHavoc(HavocStatement havoc) {
		for (VariableLHS lhs : havoc.getIdentifiers()) {
			assert lhs.getDeclarationInformation() != null : " no declaration information";
			String name = lhs.getIdentifier();
			DeclarationInformation declInfo = lhs.getDeclarationInformation();
			BoogieVar boogieVar = getModifiableBoogieVar(name, declInfo);
			assert (boogieVar != null);
			getOrConstuctCurrentRepresentative(boogieVar);
//			if (!inVars.containsKey(boogieVar)) {
//				if (!outVars.containsKey(boogieVar)) {
//					TermVariable tv = createInVar(boogieVar);
//					outVars.put(boogieVar, tv);
//				}
//			}
			if (inVars.containsKey(boogieVar)) {
				removeInVar(boogieVar);
			}
		}
		assert (assumes.toString() instanceof Object);
	}

	public void addAssume(AssumeStatement assume) {
		IdentifierTranslator[] its = getIdentifierTranslatorsIntraprocedural();
		
		Term f = (new Expression2Term( its, m_Script, m_TypeSortTranslator, assume.getFormula())).getTerm(); 
				
		assumes = Util.and(m_Script, f, assumes);
		asserts = Util.implies(m_Script, f, asserts);
		assert (assumes.toString() instanceof Object);
	}

	public void addAssert(AssertStatement assertstmt) {
		IdentifierTranslator[] its = getIdentifierTranslatorsIntraprocedural();
		
		Term f = (new Expression2Term( its, m_Script, m_TypeSortTranslator, assertstmt.getFormula())).getTerm(); 
		
		assumes = Util.and(m_Script, f, assumes);
		asserts = Util.and(m_Script, f, asserts);
		assert (assumes.toString() instanceof Object);
	}

	public void addSummary(CallStatement call) {
		assert (assumes.toString() instanceof Object);
		Procedure procedure = m_BoogieDeclarations.getProcSpecification().get(call.getMethodName());

		HashMap<String, Term> substitution = new HashMap<String, Term>();
		Expression[] arguments = call.getArguments();
		int offset;
		VariableLHS[] callLhs = call.getLhs();
		offset = 0;
		ArrayList<BoogieVar> callLhsBvs = new ArrayList<BoogieVar>();
		for (VarList outParamVl : procedure.getOutParams()) {
			for (String outParamId : outParamVl.getIdentifiers()) {
				String callLhsId = callLhs[offset].getIdentifier();
				DeclarationInformation callLhsDeclInfo = 
						callLhs[offset].getDeclarationInformation();
				BoogieVar callLhsBv = getModifiableBoogieVar(callLhsId, callLhsDeclInfo);
				assert (callLhsBv != null);
				TermVariable callLhsTv = getOrConstuctCurrentRepresentative(callLhsBv);

				substitution.put(outParamId, callLhsTv);
				callLhsBvs.add(callLhsBv);
				offset++;
			}
		}

		for (BoogieVar bv : callLhsBvs) {
			removeInVar(bv);
		}

		
		Map<BoogieVar, Term> requiresSubstitution = new HashMap<BoogieVar, Term>();
		Map<BoogieVar, Term> ensuresSubstitution = new HashMap<BoogieVar, Term>();

		for (Specification spec : procedure.getSpecification()) {
			if (spec instanceof ModifiesSpecification) {
				for (VariableLHS var : ((ModifiesSpecification) spec).getIdentifiers()) {
					String id = var.getIdentifier();
					BoogieVar boogieVar = m_Boogie2SmtSymbolTable.getBoogieVar(id, var.getDeclarationInformation(), false);
					BoogieVar boogieOldVar = m_Boogie2SmtSymbolTable.getBoogieVar(id, var.getDeclarationInformation(), true);
					assert boogieVar != null;
					assert boogieOldVar != null;
					TermVariable tvAfter = getOrConstuctCurrentRepresentative(boogieVar);
					removeInVar(boogieVar);
					
					TermVariable tvBefore = m_VariableManager.constructFreshTermVariable(boogieVar);
					inVars.put(boogieVar, tvBefore);
					ensuresSubstitution.put(boogieVar, tvAfter);
					ensuresSubstitution.put(boogieOldVar, tvBefore);
					requiresSubstitution.put(boogieVar, tvBefore);
					requiresSubstitution.put(boogieOldVar, tvBefore);

				}
			}
		}

		// generation++;
		
		Term[] argumentTerms;
		{
			IdentifierTranslator[] its = getIdentifierTranslatorsIntraprocedural();
			argumentTerms = (new Expression2Term( its, m_Script, m_TypeSortTranslator, arguments)).getTerms();
		}

		offset = 0;
		for (VarList vl : procedure.getInParams()) {
			for (String id : vl.getIdentifiers()) {
				substitution.put(id, argumentTerms[offset++]);
			}
		}

		// HashMap<BoogieVar, TermVariable> callerOldGlobals = inVarsOldGlobals;
//		HashMap<String, BoogieVar> oldLocals = m_CurrentLocals;
//		m_CurrentLocals = new HashMap<String, BoogieVar>();


		IdentifierTranslator[] ensIts = new IdentifierTranslator[] { 
				new SubstitutionTranslatorId(substitution),
				new SubstitutionTranslatorBoogieVar(ensuresSubstitution),
				new GlobalVarTranslatorWithInOutVarManagement(m_CurrentProcedure, false),
				m_Boogie2SMT.getConstOnlyIdentifierTranslator() 
				};
		
		for (Specification spec : procedure.getSpecification()) {
			if (spec instanceof EnsuresSpecification) {
				Expression post = ((EnsuresSpecification) spec).getFormula();
				Term f = (new Expression2Term( ensIts, m_Script, m_TypeSortTranslator, post)).getTerm();
				assumes = Util.and(m_Script, f, assumes);
				if (spec.isFree()) {
					asserts = Util.implies(m_Script, f, asserts);
				} else {
					asserts = Util.and(m_Script, f, asserts);
				}
			}
		}
		
		IdentifierTranslator[] reqIts = new IdentifierTranslator[] { 
				new SubstitutionTranslatorId(substitution),
				new SubstitutionTranslatorBoogieVar(requiresSubstitution),
				new GlobalVarTranslatorWithInOutVarManagement(m_CurrentProcedure, false),
				m_Boogie2SMT.getConstOnlyIdentifierTranslator() 
				};

		for (Specification spec : procedure.getSpecification()) {
			if (spec instanceof RequiresSpecification) {
				Expression pre = ((RequiresSpecification) spec).getFormula();
				Term f = (new Expression2Term( reqIts, m_Script, m_TypeSortTranslator, pre)).getTerm();
				assumes = Util.and(m_Script, f, assumes);
				if (spec.isFree()) {
					asserts = Util.implies(m_Script, f, asserts);
				} else {
					asserts = Util.and(m_Script, f, asserts);
				}
			}
		}
		assert (assumes.toString() instanceof Object);
	}
	
	

	

	/**
	 * Remove boogieVars from inVars mapping, if the inVar is not an outVar, add
	 * it to he auxilliary variables auxVar.
	 */
	private void removeInVar(BoogieVar boogieVar) {
		TermVariable tv = inVars.remove(boogieVar);
		if (outVars.get(boogieVar) != tv) {
			auxVars.add(tv);
		}
	}

	public HashMap<BoogieVar, TermVariable> getInVars() {
		return inVars;
	}

	public HashMap<BoogieVar, TermVariable> getOutVars() {
		return outVars;
	}

	public HashSet<TermVariable> getAllVars() {
		return allVars;
	}

	public Set<TermVariable> getAuxVars() {
		return auxVars;
	}

	public Term getAssumes() {
		assert (assumes.toString() instanceof Object);
		return assumes;
	}

	public Term getAsserts() {
		return asserts;
	}
	
	
	private TermVariable getOrConstuctCurrentRepresentative(BoogieVar bv) {
		TermVariable tv = inVars.get(bv);
		if (tv == null) {
			tv = createInVar(bv);
			if (!outVars.containsKey(bv)) {
				outVars.put(bv, tv);
			}
		}
		return tv;
	}


	
	/**
	 * Construct fresh TermVariable for BoogieVar bv and add it to inVars.
	 * Special case: If BoogieVar bv is an oldVar we do not take a fresh
	 * TermVariable but the default TermVariable for this BoogieVar. 
	 */
	private TermVariable createInVar(BoogieVar bv) {
		TermVariable tv;
		if (bv.isOldvar()) {
			tv = bv.getTermVariable();
		} else {
			tv = m_VariableManager.constructFreshTermVariable(bv);
		}
		inVars.put(bv, tv);
		allVars.add(tv);
		return tv;
	}
	
	public abstract class IdentifierTranslatorWithInOutVarManagement implements IdentifierTranslator {

		@Override
		public Term getSmtIdentifier(String id,
				DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode) {
			BoogieVar bv = getBoogieVar(id, declInfo, isOldContext, boogieASTNode);
			if (bv == null) {
				return null;
			} else {
				TermVariable tv = getOrConstuctCurrentRepresentative(bv);
				return tv;
			}
		}
		
		abstract protected BoogieVar getBoogieVar(String id,
				DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode);

	}
	
	public class LocalVarTranslatorWithInOutVarManagement extends IdentifierTranslatorWithInOutVarManagement {

		@Override
		protected BoogieVar getBoogieVar(String id,
				DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode) {
			StorageClass storageClass = declInfo.getStorageClass();
			switch (storageClass) {
			case IMPLEMENTATION_INPARAM:
			case IMPLEMENTATION_OUTPARAM:
			case PROCEDURE_INPARAM:
			case PROCEDURE_OUTPARAM:
			case LOCAL:
				return m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, isOldContext);
			case GLOBAL:
				return null;
			case IMPLEMENTATION:
			case PROCEDURE:
			case QUANTIFIED:
			default:
				throw new AssertionError();
			}
		}
	}
	
	public class GlobalVarTranslatorWithInOutVarManagement extends IdentifierTranslatorWithInOutVarManagement {
		private final String m_CurrentProcedure;
		private final boolean m_AllNonOld; 
		
		public GlobalVarTranslatorWithInOutVarManagement(String currentProcedure, boolean allNonOld) {
			m_CurrentProcedure = currentProcedure;
			m_AllNonOld = allNonOld;
			
		}

		@Override
		protected BoogieVar getBoogieVar(String id,
				DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode) {
			StorageClass storageClass = declInfo.getStorageClass();
			switch (storageClass) {
			case IMPLEMENTATION_INPARAM:
			case IMPLEMENTATION_OUTPARAM:
			case PROCEDURE_INPARAM:
			case PROCEDURE_OUTPARAM:
			case LOCAL:
				return null;
			case GLOBAL:
				BoogieVar bv;
				if (isOldContext) {
					if (m_AllNonOld || !modifiableByCurrentProcedure(id)) {
						bv = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, false);
					} else {
						bv = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, true);
					}
				} else {
					bv = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, false);
				}
				return bv;
			case IMPLEMENTATION:
			case PROCEDURE:
			case QUANTIFIED:
			default:
				throw new AssertionError();
			}
		}
		private boolean modifiableByCurrentProcedure(String id) {
			return true;
		}
		
	}
	
	public class SubstitutionTranslatorId implements IdentifierTranslator {
		private final Map<String, Term> m_Substitution;
		
		public SubstitutionTranslatorId(Map<String, Term> substitution) {
			super();
			m_Substitution = substitution;
		}

		@Override
		public Term getSmtIdentifier(String id,
				DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode) {
			return m_Substitution.get(id);
		}
	}
	
	public class SubstitutionTranslatorBoogieVar implements IdentifierTranslator {
		private final Map<BoogieVar, Term> m_Substitution;

		public SubstitutionTranslatorBoogieVar(Map<BoogieVar, Term> substitution) {
			super();
			m_Substitution = substitution;
		}

		@Override
		public Term getSmtIdentifier(String id,
				DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode) {
			BoogieVar bv = m_Boogie2SmtSymbolTable.getBoogieVar(id, declInfo, isOldContext);
			if (bv == null) {
				return null;
			} else 
				return m_Substitution.get(bv);
		}
	}
	
	
	public TransFormula getTransFormula(boolean simplify){
		Set<TermVariable> auxVars = getAuxVars();
		Term formula = getAssumes();
		formula = eliminateAuxVars(getAssumes(),auxVars);

		if (simplify) {
			formula = (new SimplifyDDA(m_Script)).
					getSimplifiedTerm(formula);
		} else {
			LBool isSat = Util.checkSat(m_Script, formula);
			if (isSat == LBool.UNSAT) {
				formula = m_Script.term("false");
			}
		}

		Infeasibility infeasibility;
		if (formula == m_Boogie2SMT.getScript().term("false")) {
			infeasibility = Infeasibility.INFEASIBLE;
		} else {
			infeasibility = Infeasibility.UNPROVEABLE;
		}

		TransFormula.removeSuperfluousVars(formula, inVars, outVars, auxVars);
		HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, m_Boogie2SMT);
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
				new NaiveDestructiveEqualityResolution(m_Boogie2SMT.getScript());
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
	public TransFormula inParamAssignment(CallStatement st) {
		String callee = st.getMethodName();
		Term formula = m_Boogie2SMT.getScript().term("true");
		Procedure calleeImpl = m_BoogieDeclarations.getProcImplementation().get(callee); 
		
		
		IdentifierTranslator[] its = getIdentifierTranslatorsIntraprocedural();
		Term[] argTerms = (new Expression2Term( its, m_Script, m_TypeSortTranslator, st.getArguments())).getTerms();
		outVars.clear();

		int offset = 0;
		for (VarList varList : calleeImpl.getInParams()) {
			IType type = varList.getType().getBoogieType();
			Sort sort = m_Boogie2SMT.getTypeSortTranslator().getSort(type, varList);
			for (String var : varList.getIdentifiers()) {
				BoogieVar boogieVar = m_Boogie2SMT.getBoogie2SmtSymbolTable().getBoogieVar(var, new DeclarationInformation(StorageClass.PROCEDURE_INPARAM, callee), false);
//				BoogieVar boogieVar = m_Boogie2SMT.getBoogie2SmtSymbolTable().getBoogieVar(var, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, callee), false);
				assert boogieVar != null;
						//m_Boogie2smt.getLocalBoogieVar(callee, var);
				String varname = callee + "_" + var + "_" + "InParam";
				TermVariable tv = m_Boogie2SMT.getScript().variable(varname, sort);
				outVars.put(boogieVar,tv);
				Term assignment = m_Boogie2SMT.getScript().term("=", tv, argTerms[offset]);
				formula = Util.and(m_Boogie2SMT.getScript(), formula, assignment);
				offset++;
			}
		}
		assert (st.getArguments().length == offset);
//		m_Boogie2smt.removeLocals(calleeImpl);
		allVars.addAll(outVars.values());
		HashSet<TermVariable> branchEncoders = new HashSet<TermVariable>(0);
		Term closedFormula = TransFormula.computeClosedFormula(
				formula, inVars, outVars, auxVars, m_Boogie2SMT);
		return new TransFormula(formula, inVars, outVars, 
				auxVars, branchEncoders, 
				TransFormula.Infeasibility.UNPROVEABLE,closedFormula);
	}

}