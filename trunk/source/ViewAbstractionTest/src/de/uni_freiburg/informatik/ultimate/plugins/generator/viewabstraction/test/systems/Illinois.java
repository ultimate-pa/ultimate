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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.BroadcastRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ConditionalBroadcast;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalRule.Quantifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalRule.Range;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule.RuleInstance;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.LocalRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.RendezVous;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.InstanceListIndependence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.ViewTest;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.ViewTest.ITestProgram;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Illinois implements ITestProgram<Configuration<Illinois.Ill>> {
	public enum Ill {
		invd, dirt, shrd, vlid
	}

	private static final IRule<Configuration<Ill>> t1 = new RendezVous<>(Ill.invd, Ill.shrd, Ill.dirt, Ill.shrd);
	private static final IRule<Configuration<Ill>> t2 =
			new GlobalRule<>(Ill.invd, Ill.vlid, Range.DISTINCT, Quantifier.FORALL, x -> x == Ill.invd);
	private static final IRule<Configuration<Ill>> t3 = new BroadcastRule<>(Ill.invd, Ill.dirt, x -> Ill.invd);
	private static final IRule<Configuration<Ill>> t4 = new LocalRule<>(Ill.dirt, Ill.invd);
	private static final IRule<Configuration<Ill>> t5 = new ConditionalBroadcast<>(Ill.invd, Ill.shrd, Range.DISTINCT,
			Quantifier.EXISTS, s -> s == Ill.vlid || s == Ill.shrd, s -> s == Ill.vlid ? Ill.shrd : s);
	private static final IRule<Configuration<Ill>> t6 =
			new BroadcastRule<>(Ill.shrd, Ill.dirt, x -> x == Ill.shrd ? Ill.invd : x);
	private static final IRule<Configuration<Ill>> t7 = new LocalRule<>(Ill.shrd, Ill.invd);
	private static final IRule<Configuration<Ill>> t8 = new LocalRule<>(Ill.vlid, Ill.invd);
	private static final IRule<Configuration<Ill>> t9 = new LocalRule<>(Ill.vlid, Ill.dirt);

	// manually determined; likely incomplete
	private static final List<Pair<IRule<Configuration<Ill>>, IRule<Configuration<Ill>>>> comm =
			List.of(new Pair<>(t2, t4), new Pair<>(t2, t7), new Pair<>(t2, t8), new Pair<>(t4, t6), new Pair<>(t4, t7),
					new Pair<>(t4, t8), new Pair<>(t4, t9), new Pair<>(t5, t7), new Pair<>(t6, t8), new Pair<>(t6, t9),
					new Pair<>(t7, t3), new Pair<>(t7, t4), new Pair<>(t7, t6), new Pair<>(t7, t8), new Pair<>(t7, t9),
					new Pair<>(t8, t3), new Pair<>(t8, t4), new Pair<>(t8, t6), new Pair<>(t8, t7), new Pair<>(t8, t9),
					new Pair<>(t9, t3), new Pair<>(t9, t4), new Pair<>(t9, t6), new Pair<>(t9, t7), new Pair<>(t9, t8)

			);

	public <S> IIndependenceRelation<S, RuleInstance<Configuration<Ill>>> getIndependence() {
		return new InstanceListIndependence<>(comm);
	}

	@Override
	public Program<Configuration<Ill>> getTransitions() {
		return new Program<>(List.of(t1, t2, t3, t4, t5, t6, t7, t8, t9));
	}

	@Override
	public Configuration<Ill> init(final int parameter) {
		return new Configuration<>(ViewTest.repeat(parameter, Ill.invd));
	}

	@Override
	public boolean isBad(final Configuration<Ill> config) {
		return config.stream().filter(x -> x == Ill.dirt || x == Ill.shrd).limit(2).count() >= 2
				&& config.stream().anyMatch(Ill.dirt::equals);
	}
}