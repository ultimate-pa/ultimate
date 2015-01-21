package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;

/**
 * Check if each edge of automaton is inductive (resp. if inductivity can be
 * refuted if <i>antiInductivity</i> is set).
 * 
 * @param antiInductivity
 *            if false, we check if each edge is inductive, if true we check if
 *            inductivity of each edge can be refuted.
 * @param assertInductivity
 *            if true, assert statements require inductivity (resp.
 *            anti-inductivity)
 */
public class InductivityCheck {

	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	

	private final INestedWordAutomaton<CodeBlock, IPredicate> nwa;
	
	private final IncrementalHoareTripleChecker m_IncrementalHoareTripleChecker;
	private final boolean m_AntiInductivity;
	private final boolean m_AssertInductivity;
	private final int[] yield = new int[3];
	private final boolean m_Result;

	public InductivityCheck(INestedWordAutomaton<CodeBlock, IPredicate> m_Nwa, SmtManager smtManager, ModifiableGlobalVariableManager modGlobVarManager,
			boolean m_AntiInductivity, boolean m_AssertInductivity, IUltimateServiceProvider services) {
		super();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		this.nwa = m_Nwa;
		this.m_IncrementalHoareTripleChecker = new IncrementalHoareTripleChecker(smtManager, modGlobVarManager);
		this.m_AntiInductivity = m_AntiInductivity;
		this.m_AssertInductivity = m_AssertInductivity;
		m_Result = checkInductivity();
	}

	public boolean getResult() {
		return m_Result;
	}

	private boolean checkInductivity() {
		if (m_AntiInductivity) {
			m_Logger.debug("Start checking anti-inductivity of automaton");
		} else {
			m_Logger.debug("Start checking inductivity of automaton");
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

		for (IPredicate state : nwa.getStates()) {
			for (CodeBlock cb : nwa.lettersInternal(state)) {
				for (OutgoingInternalTransition<CodeBlock, IPredicate> outTrans : nwa.internalSuccessors(state, cb)) {
					Validity inductivity = m_IncrementalHoareTripleChecker.checkInternal(state, cb, outTrans.getSucc());
					evaluateResult(inductivity, state, outTrans);
				}
			}
			for (CodeBlock cb : nwa.lettersCall(state)) {
				for (OutgoingCallTransition<CodeBlock, IPredicate> outTrans : nwa.callSuccessors(state, cb)) {
					Validity inductivity = m_IncrementalHoareTripleChecker.checkCall(state, cb, outTrans.getSucc());
					evaluateResult(inductivity, state, outTrans);
				}
			}
			for (CodeBlock cb : nwa.lettersReturn(state)) {
				for (IPredicate hier : nwa.hierPred(state, cb)) {
					for (OutgoingReturnTransition<CodeBlock, IPredicate> outTrans : nwa.returnSucccessors(state, hier,
							cb)) {
						Validity inductivity = m_IncrementalHoareTripleChecker.checkReturn(state, hier, cb, outTrans.getSucc());
						evaluateResult(inductivity, state, outTrans);
					}
				}
			}
		}
		m_IncrementalHoareTripleChecker.clearAssertionStack();
		m_Logger.info("Interpolant automaton has " + (yield[0] + yield[1] + yield[2]) + " edges. " + yield[0]
				+ " inductive. " + yield[1] + " not inductive. " + yield[2] + " times theorem prover too"
				+ " weak to decide inductivity. ");
		return result;
	}

	private boolean evaluateResult(Validity inductivity, IPredicate state, Object trans) {
		boolean result = true;
		switch (inductivity) {
		case VALID: {
			yield[0]++;
			if (m_AntiInductivity) {
				m_Logger.warn("Transition " + state + " " + trans + " not anti inductive");
				result = false;
				assert !m_AssertInductivity || result : "anti inductivity failed";
			}
			break;
		}
		case INVALID: {
			yield[1]++;
			if (!m_AntiInductivity) {
				m_Logger.warn("Transition " + state + " " + trans + " not inductive");
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
