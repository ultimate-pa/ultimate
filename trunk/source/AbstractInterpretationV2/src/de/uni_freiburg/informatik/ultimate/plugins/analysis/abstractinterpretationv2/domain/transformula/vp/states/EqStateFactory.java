/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class EqStateFactory<ACTION extends IIcfgTransition<IcfgLocation>> {

	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final EqConstraintFactory<ACTION, EqNode, EqFunction> mEqConstraintFactory;
	private final IIcfgSymbolTable mSymbolTable;
	private EqState<ACTION> mTopStateWithEmptyPvocs;

	public EqStateFactory(final EqNodeAndFunctionFactory eqNodeAndFunctionFactory,
			final EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory,
			final IIcfgSymbolTable symbolTable) {
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		mEqConstraintFactory = eqConstraintFactory;
		mSymbolTable = symbolTable;
	}

	public EqState<ACTION> disjoinAll(final Set<EqState<ACTION>> statesForCurrentEc) {
		final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> disjunctiveConstraint =
				mEqConstraintFactory.getDisjunctiveConstraint(
						statesForCurrentEc.stream()
								.map(state -> state.getConstraint())
								.collect(Collectors.toSet()));
		final EqConstraint<ACTION, EqNode, EqFunction> flattenedConstraint = disjunctiveConstraint.flatten();
		return getEqState(flattenedConstraint, flattenedConstraint.getPvocs(mSymbolTable));
	}

	public EqState<ACTION> getTopState() {
		if (mTopStateWithEmptyPvocs == null) {
			mTopStateWithEmptyPvocs = getEqState(mEqConstraintFactory.getEmptyConstraint(), Collections.emptySet());
		}
		return mTopStateWithEmptyPvocs;
	}

	public EqNodeAndFunctionFactory getEqNodeAndFunctionFactory() {
		return mEqNodeAndFunctionFactory;
	}

	public <NODE extends IEqNodeIdentifier<NODE, FUNCTION>, FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>>
		EqState<ACTION> getEqState(final EqConstraint<ACTION, NODE, FUNCTION> constraint,
				final Set<IProgramVarOrConst> variables) {
		// TODO something smarter
		return new EqState<>((EqConstraint<ACTION, EqNode, EqFunction>) constraint,
				mEqNodeAndFunctionFactory, this, variables);
	}

	public EqConstraintFactory<ACTION, EqNode, EqFunction> getEqConstraintFactory() {
		return mEqConstraintFactory;
	}

	public IIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

}
