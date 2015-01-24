package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.GlobalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker.EdgeCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class IncrementalHoareTripleChecker implements IHoareTripleChecker {
	
	private final SmtManager m_SmtManager;
	private final Script m_Script;
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	
	private IPredicate m_AssertedState;
	private IPredicate m_AssertedHier;
	private CodeBlock m_AssertedCodeBlock;
	private TransFormula m_TransFormula;
	private ScopedHashMap<BoogieVar, Term> m_HierConstants;
	public final static boolean m_AddDebugInformation = !false;
	public final static boolean m_UnletTerms = true;
	
	private final EdgeCheckerBenchmarkGenerator m_EdgeCheckerBenchmark;
	
	private static final String s_StartEdgeCheck = "starting to check validity of Hoare triples";
	private static final String s_EndEdgeCheck = "finished to check validity of Hoare triples";
	
	public IncrementalHoareTripleChecker(SmtManager smtManager, 
			ModifiableGlobalVariableManager modGlobVarManager) {
		m_SmtManager = smtManager;
		m_ModifiableGlobalVariableManager = modGlobVarManager;
		m_Script = smtManager.getScript();
		m_EdgeCheckerBenchmark = new EdgeCheckerBenchmarkGenerator();
	}
	
//	public SmtManager getSmtManager() {
//		return m_SmtManager;
//	}
	
	@Override
	public EdgeCheckerBenchmarkGenerator getEdgeCheckerBenchmark() {
		return m_EdgeCheckerBenchmark;
	}
	
	
	@Override
	public Validity checkInternal(IPredicate pre, CodeBlock cb, IPredicate succ) {
		if (m_AssertedHier != null) {
			this.unAssertHierPred();
			m_AssertedHier = null;
		}
		if (m_AssertedState != pre || m_AssertedCodeBlock != cb) {
			if (m_AssertedState != null) {
				this.unAssertPrecondition();
			}
			if (m_AssertedCodeBlock != cb) {
				if (m_AssertedCodeBlock != null) {
					this.unAssertCodeBlock();
				}
				this.assertCodeBlock(cb);
				m_AssertedCodeBlock = cb;
			}
			LBool quickCheck = this.assertPrecondition(pre);
			m_AssertedState = pre;
			if (quickCheck == LBool.UNSAT) {
				return Validity.VALID;
			}
		}
		assert m_AssertedState == pre && m_AssertedCodeBlock == cb;
		Validity result = this.postInternalImplies(succ);
		return result;
	}
	
	
	@Override
	public Validity checkCall(IPredicate pre, CodeBlock cb, IPredicate succ) {
		if (m_AssertedHier != null) {
			this.unAssertHierPred();
			m_AssertedHier = null;
		}
		if (m_AssertedState != pre || m_AssertedCodeBlock != cb) {
			if (m_AssertedState != null) {
				this.unAssertPrecondition();
			}
			if (m_AssertedCodeBlock != cb) {
				if (m_AssertedCodeBlock != null) {
					this.unAssertCodeBlock();
				}
				this.assertCodeBlock(cb);
				m_AssertedCodeBlock = cb;
			}
			LBool quickCheck = this.assertPrecondition(pre);
			m_AssertedState = pre;
			if (quickCheck == LBool.UNSAT) {
				return Validity.VALID;
			}
		}
		assert m_AssertedState == pre && m_AssertedCodeBlock == cb;
		Validity result = this.postCallImplies(succ);
		return result;
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			CodeBlock cb, IPredicate succ) {
		if (m_AssertedHier != preHier || m_AssertedState != preLin || m_AssertedCodeBlock != cb) {
			if (m_AssertedHier != null) {
				this.unAssertHierPred();
				// set the asserted hierarchical predecessor to null
				// necessary because the quickcheck may cause a return of
				// this procedure before a new m_AssertedHier has been set
				m_AssertedHier = null;
			}
			if (m_AssertedState != preLin || m_AssertedCodeBlock != cb) {
				if (m_AssertedState != null) {
					this.unAssertPrecondition();
				}
				if (m_AssertedCodeBlock != cb) {
					if (m_AssertedCodeBlock != null) {
						this.unAssertCodeBlock();
					}
					this.assertCodeBlock(cb);
					m_AssertedCodeBlock = cb;
				}
				LBool quickCheck = this.assertPrecondition(preLin);
				m_AssertedState = preLin;
				if (quickCheck == LBool.UNSAT) {
					return Validity.VALID;
				}
			}
			LBool quickCheck = this.assertHierPred(preHier);
			m_AssertedHier = preHier;
			if (quickCheck == LBool.UNSAT) {
				return Validity.VALID;
			}
		}
		assert m_AssertedState == preLin && m_AssertedHier == preHier && m_AssertedCodeBlock == cb;
		Validity result = this.postReturnImplies(succ);
		return result;
	}
	


	public void clearAssertionStack() {
		if (m_AssertedState != null) {
			this.unAssertPrecondition();
			m_AssertedState = null;
		}
		if (m_AssertedHier != null) {
			this.unAssertHierPred();
			m_AssertedHier = null;
		}
		if (m_AssertedCodeBlock != null) {
			this.unAssertCodeBlock();
			m_AssertedCodeBlock = null;
		}
	}
	

	private LBool assertPrecondition(IPredicate p) {
		assert m_SmtManager.isLockOwner(this);
		assert m_AssertedState == null : "PrePred already asserted";
		assert m_AssertedCodeBlock != null : "Assert CodeBlock first!";
		m_AssertedState = p;
		m_EdgeCheckerBenchmark.continueEdgeCheckerTime();
		m_Script.push(1);
		if (m_AssertedCodeBlock instanceof Return) {
			m_HierConstants.beginScope();
		}
		Term predcondition = p.getClosedFormula();
		if (m_AddDebugInformation) {
			String name = "precondition";
			Annotation annot = new Annotation(":named", name);
			predcondition = m_Script.annotate(predcondition, annot);
		}
		LBool quickCheck = m_SmtManager.assertTerm(predcondition);
		String predProc = m_AssertedCodeBlock.getPreceedingProcedure();
		Set<BoogieVar> oldVarsOfModifiable = m_ModifiableGlobalVariableManager.
				getOldVarsAssignment(predProc).getAssignedVars();
		Collection<Term> oldVarEqualities = constructNonModOldVarsEquality(p.getVars(), oldVarsOfModifiable);
		if (!oldVarEqualities.isEmpty()) {
			Term nonModOldVarsEquality = Util.and(m_Script, oldVarEqualities.toArray(new Term[oldVarEqualities.size()]));
			if (m_AddDebugInformation) {
				String name = "precondNonModGlobalEquality";
				Annotation annot = new Annotation(":named", name);
				nonModOldVarsEquality = m_Script.annotate(nonModOldVarsEquality, annot);
			}
			quickCheck = m_SmtManager.assertTerm(nonModOldVarsEquality);
		}
		m_EdgeCheckerBenchmark.stopEdgeCheckerTime();
		return quickCheck;
	}
	
	
	/**
	 * Return a set of equalities such that for each oldvar old(g) that occurs
	 * in vars that is not contained in oldVarsOfModifiableGlobals there is
	 * an equality (= c_g c_old(g)) where c_g is the default constant of the 
	 * global variable g and c_old(g) is the default constant of old(g).
	 */
	private Collection<Term> constructNonModOldVarsEquality(Set<BoogieVar> vars,
			Set<BoogieVar> oldVarsOfModifiableGlobals) {
		Collection<Term> conjunction = new ArrayList<>();
		for (BoogieVar bv : vars) {
			if (bv instanceof BoogieOldVar && !oldVarsOfModifiableGlobals.contains(bv)) {
				conjunction.add(oldVarsEquality((BoogieOldVar) bv));
			}
		}
		return conjunction;
	}
	
	private Term oldVarsEquality(BoogieOldVar oldVar) {
		assert oldVar.isOldvar();
		BoogieVar nonOldVar = oldVar.getNonOldVar();
		Term equality = m_Script.term("=", oldVar.getDefaultConstant(), 
										   nonOldVar.getDefaultConstant());
		return equality;
	}
	

	private void unAssertPrecondition() {
		assert m_SmtManager.isLockOwner(this);
		assert m_AssertedState != null : "No PrePred asserted";
		m_AssertedState = null;
		m_Script.pop(1);
		if (m_AssertedCodeBlock instanceof Return) {
			m_HierConstants.endScope();
		}
		if (m_AssertedCodeBlock == null) {
			throw new AssertionError("CodeBlock is assigned first");
		}
	}
	
	
	private LBool assertCodeBlock(CodeBlock cb) {
		m_SmtManager.lock(this);
		m_Script.echo(new QuotedObject(s_StartEdgeCheck));
		assert m_AssertedCodeBlock == null : "CodeBlock already asserted";
		m_AssertedCodeBlock = cb;
		m_EdgeCheckerBenchmark.continueEdgeCheckerTime();
		m_Script.push(1);
		m_TransFormula = cb.getTransitionFormula();
		Term cbFormula = m_TransFormula.getClosedFormula();
		
		if (m_AddDebugInformation) {
			String name = "codeBlock";
			Annotation annot = new Annotation(":named", name);
			cbFormula = m_Script.annotate(cbFormula, annot);
		}
		LBool quickCheck = m_SmtManager.assertTerm(cbFormula);
		if (cb instanceof Return) {
			m_HierConstants = new ScopedHashMap<BoogieVar,Term>();
			Return ret = (Return) cb;
			Call call = ret.getCorrespondingCall();
			String proc = call.getCallStatement().getMethodName();
			TransFormula ovaTF = m_ModifiableGlobalVariableManager.
					getOldVarsAssignment(proc);
			Term ovaFormula = ovaTF.getFormula();

			//rename modifiable globals to Hier vars
			ovaFormula = renameVarsToHierConstants(ovaTF.getInVars(), ovaFormula);
			//rename oldVars of modifiable globals to default vars
			ovaFormula = renameVarsToDefaultConstants(ovaTF.getOutVars(), ovaFormula);
			if (m_UnletTerms ) {
				ovaFormula = (new FormulaUnLet()).unlet(ovaFormula);
			}
			assert ovaFormula.getFreeVars().length == 0;
			if (m_AddDebugInformation) {
				String name = "modifiableVarEquality";
				Annotation annot = new Annotation(":named", name);
				ovaFormula = m_Script.annotate(ovaFormula, annot);
			}
			quickCheck = m_SmtManager.assertTerm(ovaFormula);
			
			Set<BoogieVar> modifiableGlobals = ovaTF.getInVars().keySet();
			TransFormula callTf = call.getTransitionFormula();
			Term locVarAssign = callTf.getFormula();
			//TODO: rename non-modifiable globals to DefaultConstants
			locVarAssign = renameNonModifiableGlobalsToDefaultConstants(
					callTf.getInVars(), modifiableGlobals, locVarAssign);
			
			//rename arguments vars to Hier vars
			locVarAssign = renameVarsToHierConstants(callTf.getInVars(), locVarAssign);
			//rename proc parameter vars to DefaultConstants
			locVarAssign = renameVarsToDefaultConstants(callTf.getOutVars(), locVarAssign);
			if (m_UnletTerms ) {
				locVarAssign = (new FormulaUnLet()).unlet(locVarAssign);
			}
			assert locVarAssign.getFreeVars().length == 0;
			if (m_AddDebugInformation) {
				String name = "localVarsAssignment";
				Annotation annot = new Annotation(":named", name);
				locVarAssign = m_Script.annotate(locVarAssign, annot);
			}
			quickCheck = m_SmtManager.assertTerm(locVarAssign);
		}
		m_EdgeCheckerBenchmark.stopEdgeCheckerTime();
		return quickCheck;
	}

	
	private void unAssertCodeBlock() {
		assert m_AssertedCodeBlock != null : "No CodeBlock asserted";
		m_AssertedCodeBlock = null;
		m_HierConstants = null;
		m_Script.pop(1);
		if (m_AssertedState == null) {
			m_SmtManager.unlock(this);
			m_Script.echo(new QuotedObject(s_EndEdgeCheck));
		} else {
			throw new AssertionError("CodeBlock is unasserted last");
		}

	}
	
	
	private LBool assertHierPred(IPredicate p) {
		assert m_SmtManager.isLockOwner(this);
		assert m_AssertedCodeBlock != null : "assert Return first";
		assert m_AssertedCodeBlock instanceof Return : "assert Return first";
		assert m_AssertedHier == null : "HierPred already asserted";
		m_AssertedHier = p;
		m_EdgeCheckerBenchmark.continueEdgeCheckerTime();
		m_Script.push(1);
		m_HierConstants.beginScope();
		Term hierFormula = p.getFormula();

		
		// rename globals that are not modifiable by callee to default constants
		String callee = m_AssertedCodeBlock.getPreceedingProcedure();
		Set<BoogieVar> modifiableGlobalsCallee = m_ModifiableGlobalVariableManager.
				getModifiedBoogieVars(callee);
		hierFormula = renameNonModifiableNonOldGlobalsToDefaultConstants(
				p.getVars(), modifiableGlobalsCallee, hierFormula);
		
		// rename oldvars of globals that are not modifiable by caller to 
		// default constants of nonOldVar
		String caller = m_AssertedCodeBlock.getSucceedingProcedure();
		Set<BoogieVar> modifiableGlobalsCaller = m_ModifiableGlobalVariableManager.
				getModifiedBoogieVars(caller);
		hierFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(
				p.getVars(), modifiableGlobalsCaller, hierFormula);
		


		// rename modifiable globals of callee to default constants
//		hierFormula = renameVarsToDefaultConstants(modifiableGlobalsCallee, hierFormula);
//		//rename non-modifiable globals to default constants
//		Return ret = (Return) m_CodeBlock;
//		Call call = ret.getCorrespondingCall();
//		String proc = call.getCallStatement().getMethodName();
//		TransFormula oldVarAssignment = m_ModifiableGlobalVariableManager.
//				getOldVarsAssignment(proc);
//		Set<BoogieVar> modifiableGlobals = oldVarAssignment.getInVars().keySet();
		

		//rename vars which are assigned on return to Hier vars
		hierFormula = renameVarsToHierConstants(p.getVars(), hierFormula);
		if (m_UnletTerms ) {
			hierFormula = (new FormulaUnLet()).unlet(hierFormula);
		}
		
		
		//TODO auxvars
		assert hierFormula.getFreeVars().length == 0;
		
		if (m_AddDebugInformation) {
			String name = "hierarchicalPrecondition";
			Annotation annot = new Annotation(":named", name);
			hierFormula = m_Script.annotate(hierFormula, annot);
		}
		LBool quickCheck = m_SmtManager.assertTerm(hierFormula);
		
		// Now, we have to take care for variables g that are modifiable in the
		// caller but not in the callee.
		// In the succPred and in the hierPred they will be treated as usual
		// (i.e., nonOldVar renamed to default or primed constant depending on
		// if assigned at return or not)
		// we additionally have to state that old(g) and g both have the value
		// of g at the position before the call.
		
//		Collection<Term> calleeNonModOldVarsEqualities = 
//				constructCalleeNonModOldVarsEquality(m_PrePred.getVars(), 
//						modifiableGlobalsCaller, modifiableGlobalsCallee);
//		if (!calleeNonModOldVarsEqualities.isEmpty()) {
//			Term nonModOldVarsEquality = Util.and(m_Script, 
//					calleeNonModOldVarsEqualities.toArray(new Term[calleeNonModOldVarsEqualities.size()]));
//			if (m_AddDebugInformation) {
//				String name = "NonModGlobalEqualityForCallerCalleeDifference";
//				Annotation annot = new Annotation(":named", name);
//				nonModOldVarsEquality = m_Script.annotate(nonModOldVarsEquality, annot);
//			}
//			quickCheck = m_SmtManager.assertTerm(nonModOldVarsEquality);
//		}
		
		m_EdgeCheckerBenchmark.stopEdgeCheckerTime();
		return quickCheck;
	}
	

	/**
	 * Return a set of equalities such that for each oldvar old(g) that occurs
	 * in vars and for which the corresponding nonOldVar occurs in 
	 * modifiableGlobalsCaller but not in modifiableGlobalsCallee we add the
	 * equality (= c_old(g) c_g_hier) and
	 * for each nonOldVar that occurs in 
	 * modifiableGlobalsCaller but not in modifiableGlobalsCallee we add the
	 * equality (= c_g c_g_hier),
	 * where c_g is the default constant of the 
	 * global variable g and c_old(g) is the default constant of old(g) and
	 * c_g_hier is the constant for the nonOldVar g at the position of the
	 * hierarchical predecessor.
	 */
	private Collection<Term> constructCalleeNonModOldVarsEquality(Set<BoogieVar> vars,
			Set<BoogieVar> modifiableGlobalsCaller,
			Set<BoogieVar> modifiableGlobalsCallee) {
		if (!modifiableGlobalsCallee.containsAll(modifiableGlobalsCaller)) {
			boolean test = true;
		}
		Collection<Term> conjunction = new ArrayList<>();
		for (BoogieVar bv : vars) {
			if (bv instanceof GlobalBoogieVar) {
				BoogieNonOldVar bnov;
				if (bv instanceof BoogieOldVar) {
					bnov = ((BoogieOldVar) bv).getNonOldVar();
				} else {
					bnov = (BoogieNonOldVar) bv;
				}
				if (modifiableGlobalsCaller.contains(bnov) && 
						!modifiableGlobalsCallee.contains(bnov)) {
					Term hierConst = getOrConstructHierConstant(bnov);
					Term conjunct = SmtUtils.binaryEquality(m_Script, bv.getDefaultConstant(), hierConst);
					conjunction.add(conjunct);
				}
			}
		}
		return conjunction;
	}

	private void unAssertHierPred() {
		assert m_SmtManager.isLockOwner(this);
		assert m_AssertedHier != null : "No HierPred asserted";
		m_AssertedHier = null;
		m_Script.pop(1);
		m_HierConstants.endScope();
	}
	
	
	
	
	
	private Validity postInternalImplies(IPredicate p) {
		assert m_AssertedState != null;
		assert m_AssertedCodeBlock != null;
		m_EdgeCheckerBenchmark.continueEdgeCheckerTime();
		m_Script.push(1);
		
		//OldVars renamed (depending on modifiability)
		//All variables get index 0 
		//assigned vars (locals and globals) get index 1
		//other vars get index 0
		Set<BoogieVar> assignedVars = m_TransFormula.getAssignedVars();
		Term renamedFormula = renameVarsToPrimedConstants(assignedVars, p.getFormula());
		String succProc = m_AssertedCodeBlock.getSucceedingProcedure();
		Set<BoogieVar> modifiableGlobals = m_ModifiableGlobalVariableManager.getModifiedBoogieVars(succProc);
		renamedFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(p.getVars(), modifiableGlobals, renamedFormula);
		renamedFormula = renameVarsToDefaultConstants(p.getVars(), renamedFormula);
		if (m_UnletTerms ) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = m_Script.term("not", renamedFormula);
		if (m_AddDebugInformation) {
			String name = "negatedPostcondition";
			Annotation annot = new Annotation(":named", name);
			negation = m_Script.annotate(negation, annot);
		}
		LBool isSat = m_SmtManager.assertTerm(negation);
		
		if (isSat == LBool.UNKNOWN) {
			// quickcheck failed
			isSat = m_Script.checkSat();
		}
		switch (isSat) {
		case SAT:
			m_EdgeCheckerBenchmark.getSolverCounterSat().incIn();
			break;
		case UNKNOWN:
			m_EdgeCheckerBenchmark.getSolverCounterUnknown().incIn();
			break;
		case UNSAT:
			m_EdgeCheckerBenchmark.getSolverCounterUnsat().incIn();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		m_Script.pop(1);
		m_EdgeCheckerBenchmark.stopEdgeCheckerTime();
		return MonolithicHoareTripleChecker.lbool2validity(isSat);
	}
	
	

	private Validity postCallImplies(IPredicate p) {
		assert m_AssertedState != null;
		assert (m_AssertedCodeBlock instanceof Call);
		m_EdgeCheckerBenchmark.continueEdgeCheckerTime();
		m_Script.push(1);
		
		Set<BoogieVar> boogieVars = p.getVars();
		// rename oldVars to default constants of non-oldvars
		Term renamedFormula = renameGlobalsAndOldVarsToNonOldDefaultConstants(
												boogieVars, p.getFormula());
		// rename remaining variables
		renamedFormula = renameVarsToPrimedConstants(boogieVars, renamedFormula);
		renamedFormula = renameVarsToDefaultConstants(p.getVars(), renamedFormula);
		if (m_UnletTerms ) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = m_Script.term("not", renamedFormula);
		if (m_AddDebugInformation) {
			String name = "negatedPostcondition";
			Annotation annot = new Annotation(":named", name);
			negation = m_Script.annotate(negation, annot);
		}
		LBool isSat = m_SmtManager.assertTerm(negation);
		
		if (isSat == LBool.UNKNOWN) {
			// quickcheck failed
			isSat = m_Script.checkSat();
		}
		switch (isSat) {
		case SAT:
			m_EdgeCheckerBenchmark.getSolverCounterSat().incCa();
			break;
		case UNKNOWN:
			m_EdgeCheckerBenchmark.getSolverCounterUnknown().incCa();
			break;
		case UNSAT:
			m_EdgeCheckerBenchmark.getSolverCounterUnsat().incCa();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		m_Script.pop(1);
		m_EdgeCheckerBenchmark.stopEdgeCheckerTime();
		return MonolithicHoareTripleChecker.lbool2validity(isSat);
	}



	private Validity postReturnImplies(IPredicate p) {
		assert m_AssertedState != null;
		assert (m_AssertedCodeBlock instanceof Return);
		assert m_AssertedHier != null;
		m_EdgeCheckerBenchmark.continueEdgeCheckerTime();
		m_Script.push(1);
		m_HierConstants.beginScope();
		
		
		//rename assignedVars to primed vars
		Set<BoogieVar> assignedVars = m_TransFormula.getAssignedVars();
		Term renamedFormula = renameVarsToPrimedConstants(assignedVars, p.getFormula());
		
		String callee = m_AssertedCodeBlock.getPreceedingProcedure();
		Set<BoogieVar> modifiableGlobalsCallee = m_ModifiableGlobalVariableManager.
				getModifiedBoogieVars(callee);
		
		//rename modifiable globals to default constants
		renamedFormula = renameVarsToDefaultConstants(modifiableGlobalsCallee, renamedFormula);
		
		// rename globals that are not modifiable by callee to default constants
		renamedFormula = renameNonModifiableNonOldGlobalsToDefaultConstants(
				p.getVars(), modifiableGlobalsCallee, renamedFormula);
		
		// rename oldvars of globals that are not modifiable by caller to 
		// default constants of nonOldVar
		String caller = m_AssertedCodeBlock.getSucceedingProcedure();
		Set<BoogieVar> modifiableGlobalsCaller = m_ModifiableGlobalVariableManager.
				getModifiedBoogieVars(caller);
		renamedFormula = renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(
				p.getVars(), modifiableGlobalsCaller, renamedFormula);
		
		// rename remaining non-old Globals to default constants
//		renamedFormula = renameNonOldGlobalsToDefaultConstants(p.getVars(), renamedFormula);
		
		//rename remaining vars to Hier vars
		renamedFormula = renameVarsToHierConstants(p.getVars(), renamedFormula);
		
		if (m_UnletTerms ) {
			renamedFormula = (new FormulaUnLet()).unlet(renamedFormula);
		}
		assert renamedFormula.getFreeVars().length == 0;
		Term negation = m_Script.term("not", renamedFormula);

		if (m_AddDebugInformation) {
			String name = "negatedPostcondition";
			Annotation annot = new Annotation(":named", name);
			negation = m_Script.annotate(negation, annot);
		}
		LBool isSat = m_SmtManager.assertTerm(negation);
		
		if (isSat == LBool.UNKNOWN) {
			// quickcheck failed
			isSat = m_Script.checkSat();
		}
		switch (isSat) {
		case SAT:
			m_EdgeCheckerBenchmark.getSolverCounterSat().incRe();
			break;
		case UNKNOWN:
			m_EdgeCheckerBenchmark.getSolverCounterUnknown().incRe();
			break;
		case UNSAT:
			m_EdgeCheckerBenchmark.getSolverCounterUnsat().incRe();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		m_Script.pop(1);
		m_HierConstants.endScope();
		m_EdgeCheckerBenchmark.stopEdgeCheckerTime();
		return MonolithicHoareTripleChecker.lbool2validity(isSat);
	}
	

	
	
	
	

	
	
//	private Term renameGlobalsToDefaultOldGlobalConstants(
//								Set<BoogieVar> boogieVars, Term formula) {
//		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
//		ArrayList<Term> replacers = new ArrayList<Term>();
//		for (BoogieVar bv : boogieVars) {
//			assert bv.isGlobal();
//			assert !bv.isOldvar();
//			replacees.add(bv.getTermVariable());
//			BoogieVar oldVar = m_Smt2Boogie.getOldGlobals().get(bv.getIdentifier());
//			replacers.add(oldVar.getDefaultConstant());
//		}
//		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
//		Term[] values = replacers.toArray(new Term[replacers.size()]);
//		return m_Script.let( vars , values, formula);
//	}
	
	
	private Term renameVarsToDefaultConstants(Set<BoogieVar> boogieVars, Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(bv.getDefaultConstant());
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}
	
	
	private Term renameVarsToDefaultConstants(Map<BoogieVar, TermVariable> bv2tv, Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : bv2tv.keySet()) {
			replacees.add(bv2tv.get(bv));
			replacers.add(bv.getDefaultConstant());
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}
	
	
	private Term renameVarsToPrimedConstants(Set<BoogieVar> boogieVars, Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(bv.getPrimedConstant());
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}


	private Term renameVarsToHierConstants(Set<BoogieVar> boogieVars, Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : boogieVars) {
			replacees.add(bv.getTermVariable());
			replacers.add(getOrConstructHierConstant(bv));
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}
	
	private Term renameVarsToHierConstants(Map<BoogieVar, TermVariable> bv2tv, Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : bv2tv.keySet()) {
			replacees.add(bv2tv.get(bv));
			replacers.add(getOrConstructHierConstant(bv));
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}


	private Term getOrConstructHierConstant(BoogieVar bv) {
		Term preHierConstant = m_HierConstants.get(bv);
		if (preHierConstant == null) {
			String name = "c_" + bv.getTermVariable().getName() + "_Hier";
			Sort sort = bv.getTermVariable().getSort();
			m_Script.declareFun(name, new Sort[0], sort);
			preHierConstant = m_Script.term(name);
			m_HierConstants.put(bv, preHierConstant);
		}
		return preHierConstant;
	}
	
	

	/**
	 * Rename each g in boogieVars that is not contained in modifiableGlobals
	 * to c_g, where c_g is the default constant for g.
	 */
	private Term renameNonModifiableNonOldGlobalsToDefaultConstants(
			Set<BoogieVar> boogieVars, 
			Set<BoogieVar> modifiableGlobals,
			Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : boogieVars) {
			if (bv.isGlobal()) {
				if (bv instanceof BoogieNonOldVar) {
					if (modifiableGlobals.contains(bv)) {
						//do nothing
					} else {
						replacees.add(bv.getTermVariable());
						replacers.add(bv.getDefaultConstant());
					}
				}
			}
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}
	
	
	/**
	 * Rename oldVars old(g) of non-modifiable globals to the
	 * default constants of g. 
	 */
	private Term renameNonModifiableOldGlobalsToDefaultConstantOfNonOldVar(
			Set<BoogieVar> boogieVars, 
			Set<BoogieVar> modifiableGlobals,
			Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : boogieVars) {
			if (bv instanceof BoogieOldVar) {
				BoogieNonOldVar nonOldVar = ((BoogieOldVar) bv).getNonOldVar();
				if (modifiableGlobals.contains(nonOldVar)) {
					//do nothing
				} else {
					replacees.add(bv.getTermVariable());
					replacers.add(nonOldVar.getDefaultConstant());
				}
				
			}
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}

	
	
	
	private Term renameNonModifiableGlobalsToDefaultConstants(
			Map<BoogieVar,TermVariable> boogieVars, 
			Set<BoogieVar> modifiableGlobals,
			Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : boogieVars.keySet()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					assert !modifiableGlobals.contains(bv);
					// do nothing
				} else {
					if (modifiableGlobals.contains(bv)) {
						//do noting
					} else {
						//oldVar of global which is not modifiable by called proc
						replacees.add(boogieVars.get(bv));
						replacers.add(bv.getDefaultConstant());
					}
				}
			} else {
				assert !modifiableGlobals.contains(bv);
			}
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}
	
	
	
	
	private Term renameGlobalsAndOldVarsToNonOldDefaultConstants(
			Set<BoogieVar> boogieVars, 
			Term formula) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : boogieVars) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					replacees.add(bv.getTermVariable());
					BoogieVar nonOldbv = ((BoogieOldVar) bv).getNonOldVar();
					replacers.add(nonOldbv.getDefaultConstant());
				} else {
					replacees.add(bv.getTermVariable());
					replacers.add(bv.getDefaultConstant());
				}
			}
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		return m_Script.let( vars , values, formula);
	}
	

	
	
	
	public boolean isAssertionStackEmpty() {
		if (m_AssertedCodeBlock == null) {
			assert m_AssertedState == null;
			assert m_AssertedHier == null;
			return true;
		} else {
			return false;
		}
	}


	
}
