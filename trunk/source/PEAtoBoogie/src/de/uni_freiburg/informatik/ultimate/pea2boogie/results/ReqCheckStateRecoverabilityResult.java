package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

public class ReqCheckStateRecoverabilityResult<LOC extends IElement, TE extends IAction, E> extends ReqCheckFailResult<LOC>{

	private final String mMessage;
	
	public ReqCheckStateRecoverabilityResult(final LOC element, final String plugin, final IBacktranslationService translatorSequence, final String message) {
		super(element, plugin, translatorSequence);
		mMessage = message;
	}
	
	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getShortDescription());
		sb.append(CoreUtil.getPlatformLineSeparator());
		if (mMessage != null) {
			sb.append("Verification Expression: ");
			sb.append(mMessage);
		}
		return sb.toString();
	}
}
