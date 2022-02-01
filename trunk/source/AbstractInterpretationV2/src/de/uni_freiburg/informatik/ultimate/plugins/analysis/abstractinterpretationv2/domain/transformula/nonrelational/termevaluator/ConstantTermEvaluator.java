/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;

public class ConstantTermEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE>>
		implements ITermEvaluator<VALUE, STATE> {

	private final VALUE mValue;

	public ConstantTermEvaluator(final VALUE value) {
		mValue = value;
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;
		return Collections.singletonList(new NonrelationalEvaluationResult<>(mValue, BooleanValue.TOP));
	}

	@Override
	public List<STATE> inverseEvaluate(final IEvaluationResult<VALUE> computedValue, final STATE currentState) {
		assert computedValue != null;
		assert currentState != null;
		return Collections.singletonList(currentState);
	}

	@Override
	public void addSubEvaluator(final ITermEvaluator<VALUE, STATE> evaluator) {
		throw new UnsupportedOperationException("Cannot add a sub evaluator to a constant term evaluator.");
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return Collections.emptySet();
	}

	@Override
	public boolean hasFreeOperands() {
		return false;
	}

	@Override
	public boolean containsBool() {
		return false;
	}

	@Override
	public String toString() {
		return mValue.toString();
	}
}
