package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;

/**
 * Check if each edge of automaton is inductive (resp. if inductivity can be
 * refuted if <i>antiInductivity</i> is set).
 * @param antiInductivity if false, we check if each edge is inductive, if
 * true we check if inductivity of each edge can be refuted.
 * @param assertInductivity if true, assert statements require inductivity
 * (resp. anti-inductivity)
 */
public class InductivityCheck {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private final INestedWordAutomaton<CodeBlock, IPredicate> nwa;
	private final EdgeChecker m_EdgeChecker;
	private final boolean m_AntiInductivity;
	private final boolean m_AssertInductivity;
	private final int[] yield = new int[3];
	private final boolean m_Result;
	
	public InductivityCheck(
			INestedWordAutomaton<CodeBlock, IPredicate> m_Nwa,
			EdgeChecker m_EdgeChecker, boolean m_AntiInductivity,
			boolean m_AssertInductivity) {
		super();
		this.nwa = m_Nwa;
		this.m_EdgeChecker = m_EdgeChecker;
		this.m_AntiInductivity = m_AntiInductivity;
		this.m_AssertInductivity = m_AssertInductivity;
		m_Result = checkInductivity();
	}
	
	public boolean getResult() {
		return m_Result;
	}
	
	
	

	private boolean checkInductivity() {
		if (m_AntiInductivity) {
			s_Logger.debug("Start checking anti-inductivity of automaton");
		} else {
			s_Logger.debug("Start checking inductivity of automaton");
		}
		
		boolean result = true;
		// yield[0] is the number of edges whose inductiveness could be
		// proven
		// yield[1] is the number of edges whose inductiveness could be
		// refuted
		// yield[2] is the number of edges whose inductiveness could be
		// neither proven nor refuted because theorem prover too weak
		// yield[3] is the number of edges whose inductiveness could be
		// neither proven nor refuted because there were no interpolants
		
		for(IPredicate state : nwa.getStates()) {
			for (CodeBlock cb : nwa.lettersInternal(state)) {
				m_EdgeChecker.assertCodeBlock(cb);
				m_EdgeChecker.assertPrecondition(state);
				for (OutgoingInternalTransition<CodeBlock, IPredicate> outTrans : nwa.internalSuccessors(state, cb)) {
					LBool inductivity = m_EdgeChecker.postInternalImplies(outTrans.getSucc());
					evaluateResult(inductivity, state, outTrans);
				}
				m_EdgeChecker.unAssertPrecondition();
				m_EdgeChecker.unAssertCodeBlock();
			}
			for (CodeBlock cb : nwa.lettersCall(state)) {
				m_EdgeChecker.assertCodeBlock(cb);
				m_EdgeChecker.assertPrecondition(state);
				for (OutgoingCallTransition<CodeBlock, IPredicate> outTrans : nwa.callSuccessors(state, cb)) {
					LBool inductivity = m_EdgeChecker.postCallImplies(outTrans.getSucc());
					evaluateResult(inductivity, state, outTrans);
				}
				m_EdgeChecker.unAssertPrecondition();
				m_EdgeChecker.unAssertCodeBlock();
			}
			for (CodeBlock cb : nwa.lettersReturn(state)) {
				m_EdgeChecker.assertCodeBlock(cb);
				m_EdgeChecker.assertPrecondition(state);
				for (IPredicate hier : nwa.hierPred(state, cb)) {
					m_EdgeChecker.assertHierPred(hier);
					for (OutgoingReturnTransition<CodeBlock, IPredicate> outTrans : nwa.returnSucccessors(state, hier, cb)) {
						LBool inductivity = m_EdgeChecker.postReturnImplies(outTrans.getSucc());
						evaluateResult(inductivity, state, outTrans);
					}
					m_EdgeChecker.unAssertHierPred();
				}
				m_EdgeChecker.unAssertPrecondition();
				m_EdgeChecker.unAssertCodeBlock();
			}

			
		}
		s_Logger.info("Interpolant automaton has " + (yield[0]+yield[1]+yield[2]) + 
				" edges. " + yield[0] + " inductive. " + yield[1] +
				" not inductive. " +	yield[2]+ " times theorem prover too" +
				" weak to decide inductivity. ");
		return result;
	}



	private boolean evaluateResult(LBool inductivity, IPredicate state, Object trans) {
		boolean result = true;
		switch (inductivity) {
		case UNSAT: {
			yield[0]++;
			if (m_AntiInductivity) {
				s_Logger.warn("Transition "+ state + " " + trans + " not anti inductive");
				result = false;
				assert !m_AssertInductivity || result : "anti inductivity failed";
			}
			break;
		}
		case SAT: {
			yield[1]++;
			if (!m_AntiInductivity) {
				s_Logger.warn("Transition "+ state + " " + trans + " not inductive");
				result = false;
				assert !m_AssertInductivity || result : "inductivity failed";
			}
			break;
		}
		case UNKNOWN: {
			yield[2]++;
			break;
		}
		default:
			throw new IllegalArgumentException();
		}
		return result;
	}
}
