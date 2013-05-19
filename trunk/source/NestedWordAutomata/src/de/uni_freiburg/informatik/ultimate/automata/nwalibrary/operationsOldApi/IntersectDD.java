package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class IntersectDD<LETTER, STATE> extends AbstractIntersect<LETTER, STATE>
		implements IOperation {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	public IntersectDD(INestedWordAutomatonOldApi<LETTER, STATE> fstNwa,
			INestedWordAutomatonOldApi<LETTER, STATE> sndNwa)
			throws OperationCanceledException {
		super(false, false, fstNwa, sndNwa);
	}

	public IntersectDD(boolean minimizeResult,
			INestedWordAutomatonOldApi<LETTER, STATE> fstNwa,
			INestedWordAutomatonOldApi<LETTER, STATE> sndNwa)
			throws OperationCanceledException {
		super(false, minimizeResult, fstNwa, sndNwa);
	}

	@Override
	public String operationName() {
		return "intersect";
	}

}
