/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.FormulaToEqDisjunctiveConstraintConverter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.WeqSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

/**
 * Domain of equalities
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class EqDomain extends StateBasedDomain<EqState> {
	// TODO: Make this a setting?
	private static final boolean DISABLE_WEAK_EQUIVALENCES = true;

	public EqDomain(final SymbolicTools tools, final int maxDisjuncts, final IUltimateServiceProvider services) {
		super(tools, maxDisjuncts, new EqStateProvider(services, tools.getManagedScript()));
	}

	private static class EqStateProvider implements IStateProvider<EqState> {
		private final IUltimateServiceProvider mServices;
		private final EqConstraintFactory<EqNode> mEqConstraintFactory;
		private final EqNodeAndFunctionFactory mEqFactory;
		private final ManagedScript mManagedScript;

		public EqStateProvider(final IUltimateServiceProvider services, final ManagedScript managedScript) {
			mServices = services;
			mManagedScript = managedScript;
			mEqFactory = new EqNodeAndFunctionFactory(services, managedScript, Set.of(), null, Set.of());
			final WeqSettings settings = new WeqSettings();
			settings.setDeactivateWeakEquivalences(DISABLE_WEAK_EQUIVALENCES);
			mEqConstraintFactory =
					new EqConstraintFactory<>(mEqFactory, services, managedScript, settings, false, Set.of());
		}

		@Override
		public List<EqState> toStates(final IPredicate pred) {
			// TODO: This does not use the timeout, should we add this?
			final EqDisjunctiveConstraint<EqNode> converted = new FormulaToEqDisjunctiveConstraintConverter(mServices,
					mManagedScript, mEqConstraintFactory, mEqFactory, pred.getFormula()).getResult();
			return converted.getConstraints().stream().map(EqState::new).collect(Collectors.toList());
		}
	}
}
