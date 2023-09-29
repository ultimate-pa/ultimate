package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class FilteredIcfgTransformer<LOC extends IcfgLocation> implements IIcfgTransformer<LOC> {
	private final BasicIcfg<LOC> mResultIcfg;

	public FilteredIcfgTransformer(final IIcfg<LOC> icfg, final String newIdentifier, final Class<LOC> locationClass,
			final ILocationFactory<LOC, LOC> funLocFac, final ILogger logger,
			final IcfgTransformationBacktranslator backtranslationTracker, final Predicate<IcfgEdge> edgeFilter,
			final Predicate<LOC> locationFilter) {
		mResultIcfg = new BasicIcfg<>(newIdentifier, icfg.getCfgSmtToolkit(), locationClass);
		final TransformedIcfgBuilder<LOC, LOC> lst =
				new TransformedIcfgBuilder<>(logger, funLocFac, backtranslationTracker, icfg, mResultIcfg);
		processIcfg(icfg.getInitialNodes(), lst, edgeFilter, locationFilter);
	}

	public FilteredIcfgTransformer(final IIcfg<LOC> icfg, final String newIdentifier, final Class<LOC> locationClass,
			final ILocationFactory<LOC, LOC> funLocFac, final ILogger logger,
			final IcfgTransformationBacktranslator backtranslationTracker, final Predicate<IcfgEdge> edgeFilter) {
		this(icfg, newIdentifier, locationClass, funLocFac, logger, backtranslationTracker, edgeFilter, x -> true);
	}

	private void processIcfg(final Set<LOC> init, final TransformedIcfgBuilder<LOC, LOC> lst,
			final Predicate<IcfgEdge> edgeFilter, final Predicate<LOC> locationFilter) {
		final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(init);

		// we need to create new return transitions after new call transitions have been created
		final List<Triple<LOC, LOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		while (iter.hasNext()) {
			final LOC oldSource = iter.next();
			if (!locationFilter.test(oldSource)) {
				continue;
			}
			final LOC newSource = lst.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				@SuppressWarnings("unchecked")
				final LOC oldTarget = (LOC) oldTransition.getTarget();
				if (!locationFilter.test(oldTarget)) {
					continue;
				}
				final LOC newTarget = lst.createNewLocation(oldTarget);
				if (!edgeFilter.test(oldTransition)) {
					continue;
				}
				if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
					rtrTransitions.add(new Triple<>(newSource, newTarget, oldTransition));
				} else {
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}

		rtrTransitions.forEach(a -> lst.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

	@Override
	public IIcfg<LOC> getResult() {
		return mResultIcfg;
	}
}
