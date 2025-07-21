package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.translation.BacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CACSLBacktranslatedCFG extends BacktranslatedCFG<String, CACSLLocation> {

	public CACSLBacktranslatedCFG(final String filename,
			final List<? extends IExplicitEdgesMultigraph<?, ?, String, CACSLLocation, ?>> cfgs,
			final Class<? extends CACSLLocation> clazz) {
		super(filename, cfgs, clazz);
	}

	@Override
	public IBacktranslationValueProvider<CACSLLocation, ?> getBacktranslationValueProvider() {
		return new CACSLBacktranslationValueProvider();
	}
}
