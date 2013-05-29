package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.AbstractIntersect;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class BuchiIntersectDD<LETTER, STATE> extends
		AbstractIntersect<LETTER, STATE> implements IOperation<LETTER,STATE> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	public BuchiIntersectDD(INestedWordAutomatonOldApi<LETTER, STATE> fstNwa,
			INestedWordAutomatonOldApi<LETTER, STATE> sndNwa)
			throws AutomataLibraryException {
		super(true, false, fstNwa, sndNwa);
	}

	public BuchiIntersectDD(INestedWordAutomatonOldApi<LETTER, STATE> fstNwa,
			INestedWordAutomatonOldApi<LETTER, STATE> sndNwa,
			boolean minimizeResult)
			throws AutomataLibraryException {
		super(true, minimizeResult, fstNwa, sndNwa);
	}

	@Override
	public String operationName() {
		return "buchiIntersectDD";
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
