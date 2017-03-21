/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncoder;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.BlockEncodingPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.BlockEncodingPreferences.MinimizeStates;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Transform an {@link Icfg} by TODO
 * (Back)transform a proof for the large block encoded {@link Icfg} to a
 * proof for the original {@link Icfg} by TODO
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class BranchUnfoldIcfgTransformer {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final PredicateFactory mPredicateFactory;
	private final IPredicateUnifier mPredicateUnifier;
	/**
	 * Map that assigns to each large block encoded icfg location the corresponding location in the orginal icfg
	 */
	private Map<IcfgLocation, IcfgLocation> mLbeBacktranslation;
	private IIcfg<IcfgLocation> mInputIcfg;
	
	private final HashRelation<IcfgLocation, IcfgLocation> mOldLoc2NewLoc = new HashRelation<>();

	public BranchUnfoldIcfgTransformer(final IUltimateServiceProvider services,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
	}
	
	public IIcfg<IcfgLocation> transform(final IIcfg<IcfgLocation> inputIcfg) {
		mInputIcfg = inputIcfg;
		final IUltimateServiceProvider beServices =
				mServices.registerPreferenceLayer(getClass(), BlockEncodingPreferences.PLUGIN_ID);
		final IPreferenceProvider ups = beServices.getPreferenceProvider(BlockEncodingPreferences.PLUGIN_ID);
		ups.put(BlockEncodingPreferences.FXP_INTERPROCEDURAL_COMPOSITION, false);
		ups.put(BlockEncodingPreferences.FXP_MINIMIZE_STATES, MinimizeStates.MULTI);
		// TODO: If you remove infeasible edges, you may end up with an empty program. Either disable this or deal
		// with it.
		ups.put(BlockEncodingPreferences.FXP_REMOVE_INFEASIBLE_EDGES, false);
		final BlockEncoder blockEncoder = new BlockEncoder(mLogger, beServices, inputIcfg,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final IIcfg<IcfgLocation> outputIcfg = blockEncoder.getResult();
		assert !outputIcfg.getInitialNodes().isEmpty() : "LBE ICFG is emtpy";
		mLbeBacktranslation = blockEncoder.getBacktranslator().getLocationMapping();
		return outputIcfg;
	}
	
	public Map<IcfgLocation, IPredicate> transform(final Map<IcfgLocation, IPredicate> hoareAnnotation) {
		final Map<IcfgLocation, IPredicate> result = new HashMap<>();
		for (final IcfgLocation oldLoc : mOldLoc2NewLoc.getDomain()) {
			final List<IPredicate> preds = new ArrayList<>();
			for (final IcfgLocation newLoc : mOldLoc2NewLoc.getImage(oldLoc)) {
				preds.add(hoareAnnotation.get(newLoc));
			}
			final Term newPred = mPredicateFactory.or(false, preds);
			result.put(oldLoc, mPredicateFactory.newPredicate(newPred));
			
		}
		mLbeBacktranslation = null;
		mInputIcfg = null;
		return result;
	}

}
