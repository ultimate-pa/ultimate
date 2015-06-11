package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class AbstractInterpretationObserver extends BaseObserver {

	private final IUltimateServiceProvider mServices;

	public AbstractInterpretationObserver(IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		return false;
	}

}
