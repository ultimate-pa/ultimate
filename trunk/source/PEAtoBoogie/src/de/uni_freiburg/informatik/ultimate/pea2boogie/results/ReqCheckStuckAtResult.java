package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;


public final class ReqCheckStuckAtResult<LOC extends IElement, TE extends IAction, E>
		extends ReqCheckFailResult<LOC> {

	private final String mNvp;

	public ReqCheckStuckAtResult(final LOC element, final String plugin,final IBacktranslationService translatorSequence, final String nvp) {
		super(element, plugin, translatorSequence);
		mNvp = nvp;
	}

	public ReqCheckStuckAtResult(final LOC element, final String plugin,final IBacktranslationService translatorSequence) {
		this(element, plugin, translatorSequence,null);
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getShortDescription());
		if (mNvp != CDD.TRUE.toString()) {
			sb.append(CoreUtil.getPlatformLineSeparator());
			sb.append("Stuck at NVP: " + mNvp);
		}
		return sb.toString();
	}
}