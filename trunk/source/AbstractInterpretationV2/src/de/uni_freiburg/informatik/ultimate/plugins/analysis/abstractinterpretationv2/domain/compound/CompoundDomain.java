/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound;

import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * Implementation of the compound domain for abstract interpretation.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings("rawtypes")
public class CompoundDomain implements IAbstractDomain<CompoundDomainState, IcfgEdge> {

	private final IUltimateServiceProvider mServices;
	private final List<IAbstractDomain> mDomainList;
	private final BoogieIcfgContainer mRootAnnotation;

	private IAbstractStateBinaryOperator<CompoundDomainState> mWideningOperator;
	private IAbstractPostOperator<CompoundDomainState, IcfgEdge> mPostOperator;

	public CompoundDomain(final IUltimateServiceProvider serviceProvider, final List<IAbstractDomain> domainList,
			final BoogieIcfgContainer icfg) {
		mServices = serviceProvider;
		mDomainList = domainList;
		mRootAnnotation = icfg;
	}

	@Override
	public CompoundDomainState createTopState() {
		return new CompoundDomainState(mServices, mDomainList, false);
	}

	@Override
	public CompoundDomainState createBottomState() {
		return new CompoundDomainState(mServices, mDomainList, true);
	}

	@Override
	public IAbstractStateBinaryOperator<CompoundDomainState> getWideningOperator() {
		if (mWideningOperator == null) {
			mWideningOperator = new CompoundDomainWideningOperator(mServices);
		}
		return mWideningOperator;
	}

	@Override
	public IAbstractPostOperator<CompoundDomainState, IcfgEdge> getPostOperator() {
		if (mPostOperator == null) {
			mPostOperator = new CompoundDomainPostOperator(mServices, mRootAnnotation);
		}
		return mPostOperator;
	}

	@Override
	public String domainDescription() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(IAbstractDomain.super.domainDescription());
		stringBuilder.append(" [");
		stringBuilder.append(
				mDomainList.stream().map(domain -> domain.domainDescription()).collect(Collectors.joining(", ")));
		stringBuilder.append("]");
		return stringBuilder.toString();
	}

	@Override
	public void beforeFixpointComputation(final Object... objects) {
		for (final IAbstractDomain domain : mDomainList) {
			domain.beforeFixpointComputation(objects);
		}
	}

	@Override
	public boolean isAbstractable(final Term term) {
		return mDomainList.stream().anyMatch(d -> d.isAbstractable(term));
	}
}
