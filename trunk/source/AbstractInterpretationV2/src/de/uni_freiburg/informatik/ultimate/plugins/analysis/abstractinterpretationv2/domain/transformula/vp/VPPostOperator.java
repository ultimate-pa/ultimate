/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPStateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VpTfStateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPPostOperator<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IAbstractPostOperator<VPState<ACTION>, ACTION, IProgramVarOrConst> {
	
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	
	private final VPDomain<ACTION> mDomain;
	private final VPStateFactory<ACTION> mStateFactory;
	private final VPDomainPreanalysis mPreAnalysis;
	private final VPTransFormulaStateBuilderPreparer mTfPreparer;
	private final VpTfStateFactory mTfStateFactory;
	
	public VPPostOperator(final ManagedScript script, final IUltimateServiceProvider services,
			final VPDomain<ACTION> domain) {
		mScript = script;
		mServices = services;
		mDomain = domain;
		mStateFactory = mDomain.getVpStateFactory();
		mPreAnalysis = mDomain.getPreAnalysis();
		mTfPreparer = mDomain.getTfPreparer();
		mTfStateFactory = mDomain.getTfStateFactory();
	}
	
	/**
	 * This specific implementation of apply(..) proceeds as follows
	 * <list>
	 *  <li> create a tfState that corresponds to the given transFormula and propagate all we know about its inVars from
	 *     the oldState into it
	 *  <li> apply the TransFormula to the tfState, i.e., put it into a state where we have all the knowledge about the 
	 *       outVars that we can compute from the inVar-information from the step before and the transFormula
	 *  <li> convert the resulting tfState(s) back to "normal" states, by taking all the information about the outVars,
	 *     and overwriting the information the oldState has about them -- but leaving the information about other 
	 *     variables in the oldState intact, as the TransFormula did not touch those
	 * </list>
	 */
	@Override
	public List<VPState<ACTION>> apply(final VPState<ACTION> oldState, final ACTION transition) {

		if (mPreAnalysis.isDebugMode()) {
			mPreAnalysis.getLogger().debug("VPPostOperator: apply(..) (internal transition) (begin)");
			mPreAnalysis.getBenchmark().unpause(VPSFO.applyClock);
		}
		
		final UnmodifiableTransFormula tf = IcfgUtils.getTransformula(transition);
		if (tf.getOutVars().isEmpty()) {
			if (mPreAnalysis.isDebugMode()) {
				mPreAnalysis.getBenchmark().pause(VPSFO.applyClock);
			}
			return Collections.singletonList(oldState);
		}
		
		if (oldState.isBottom()) {
			if (mPreAnalysis.isDebugMode()) {
				mPreAnalysis.getBenchmark().pause(VPSFO.applyClock);
			}
			return Collections.singletonList(oldState);
		}
		
		final VPTfState tfState = mTfStateFactory.createTfState(oldState, transition);
		
		final Set<VPTfState> tfStatesAfterTransition = tfState.applyTransition(mTfStateFactory, mServices);
		
		final Set<VPState<ACTION>> resultStates = mStateFactory.projectToOutVars(tfStatesAfterTransition, null, null);

		if (mPreAnalysis.isDebugMode()) {
			mPreAnalysis.getLogger().debug("VPPostOperator: apply(..) (internal transition) (end)");
			mPreAnalysis.getBenchmark().pause(VPSFO.overallFromPreAnalysis);
			mPreAnalysis.getBenchmark().printResult(mPreAnalysis.getLogger());
			mPreAnalysis.getBenchmark().unpause(VPSFO.overallFromPreAnalysis);
		
			mPreAnalysis.getBenchmark().pause(VPSFO.applyClock);
		}
		assert VPDomainHelpers.containsNoNullElement(resultStates);
		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
		assert resultStates.size() < 50 : "TODO: merge internally";
		return new ArrayList<>(resultStates);
	}
	
	@Override
	public List<VPState<ACTION>> apply(final VPState<ACTION> stateBeforeLeaving,
			final VPState<ACTION> stateAfterLeaving, final ACTION transition) {

		if (transition instanceof Call
				|| transition instanceof Return) {
			final VPTfState tfState = mTfStateFactory.createTfState(stateBeforeLeaving, transition);
			final Set<VPTfState> tfStatesAfterTransition = tfState.applyTransition(mTfStateFactory, mServices);
			final Set<VPState<ACTION>> patchStates = mStateFactory.projectToOutVars(tfStatesAfterTransition, null, null);
			
			final Set<VPState<ACTION>> result = new HashSet<>();
			for (VPState<ACTION> patchState : patchStates) {
				result.add(stateAfterLeaving.patch(patchState));
			}

			assert VPDomainHelpers.containsNoNullElement(result);
			assert VPDomainHelpers.allStatesHaveSameVariables(result);
			return new ArrayList<>(result);
		} else if (transition instanceof Summary) {
			throw new AssertionError("TODO: implement"); //TODO
		} else {
			throw new AssertionError("unexpected: apply with two preStates on an edges that is not Call, Return, "
					+ "Summary");
		}
	}
}
