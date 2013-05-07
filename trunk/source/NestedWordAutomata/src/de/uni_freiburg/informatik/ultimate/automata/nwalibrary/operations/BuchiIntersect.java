package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class BuchiIntersect<LETTER, STATE> extends
		AbstractIntersect<LETTER, STATE> implements IOperation {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	public BuchiIntersect(INestedWordAutomaton<LETTER, STATE> fstNwa,
			INestedWordAutomaton<LETTER, STATE> sndNwa)
			throws OperationCanceledException {
		super(true, false, fstNwa, sndNwa);
	}

	public BuchiIntersect(INestedWordAutomaton<LETTER, STATE> fstNwa,
			INestedWordAutomaton<LETTER, STATE> sndNwa,
			boolean minimizeResult)
			throws OperationCanceledException {
		super(true, minimizeResult, fstNwa, sndNwa);
	}

	@Override
	public String operationName() {
		return "buchiIntersect";
	}

}
