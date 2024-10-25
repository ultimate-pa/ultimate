/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstractionTest Library.
 *
 * The ULTIMATE ViewAbstractionTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstractionTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstractionTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstractionTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstractionTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.BroadcastRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ConditionalBroadcast;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalRule.Quantifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalRule.Range;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.LocalRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.RendezVous;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.ViewTest;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.ViewTest.ITestProgram;

public class Firefly implements ITestProgram<Firefly.Ffl> {
	enum Ffl {
		invd, excl, shrd, dirt
	}

	@Override
	public Program<Firefly.Ffl> getTransitions() {
		return new Program<>(null, List.of(
				// t1
				new RendezVous<>(Ffl.invd, Ffl.shrd, Ffl.dirt, Ffl.shrd),
				// t2
				new GlobalRule<>(Ffl.invd, Ffl.excl, Range.DISTINCT, Quantifier.FORALL, Ffl.invd::equals),
				// t3
				new ConditionalBroadcast<>(Ffl.invd, Ffl.shrd, Range.DISTINCT, Quantifier.EXISTS,
						s -> s == Ffl.excl || s == Ffl.shrd, s -> s == Ffl.excl ? Ffl.shrd : s),
				// t4
				new LocalRule<>(Ffl.excl, Ffl.dirt),
				// t5
				new BroadcastRule<>(Ffl.invd, Ffl.dirt, s -> Ffl.invd),
				// t6
				new GlobalRule<>(Ffl.shrd, Ffl.excl, Range.DISTINCT, Quantifier.FORALL, s -> s != Ffl.shrd)));
	}

	@Override
	public Configuration<Ffl> init(final int parameter) {
		return new Configuration<>(ViewTest.repeat(parameter, Ffl.invd));
	}

	@Override
	public boolean isBad(final Configuration<Ffl> config) {
		return (config.stream().anyMatch(Ffl.dirt::equals)
				&& (config.stream().anyMatch(Ffl.shrd::equals) || config.stream().anyMatch(Ffl.excl::equals)))
				|| (config.stream().filter(Ffl.dirt::equals).count() >= 2)
				|| (config.stream().filter(Ffl.excl::equals).count() >= 2);
	}
}