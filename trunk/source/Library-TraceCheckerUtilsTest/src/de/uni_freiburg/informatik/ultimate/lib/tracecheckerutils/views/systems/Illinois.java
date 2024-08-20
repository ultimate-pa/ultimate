/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.systems;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.BroadcastRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ConditionalBroadcast;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Configuration;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Quantifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Range;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.LocalRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Program;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.RendezVous;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest.ITestProgram;

public class Illinois implements ITestProgram<Illinois.Ill> {
	public enum Ill {
		invd, dirt, shrd, vlid
	}

	@Override
	public Program<Ill> getTransitions() {
		return new Program<>(null, List.of(
				// t1
				new RendezVous<>(Ill.invd, Ill.shrd, Ill.dirt, Ill.shrd),
				// t2
				new GlobalRule<>(Ill.invd, Ill.vlid, Range.DISTINCT, Quantifier.FORALL, x -> x == Ill.invd),
				// t3
				new BroadcastRule<>(Ill.invd, Ill.dirt, x -> Ill.invd),
				// t4
				new LocalRule<>(Ill.dirt, Ill.invd),
				// t5
				new ConditionalBroadcast<>(Ill.invd, Ill.shrd, Range.DISTINCT, Quantifier.EXISTS,
						s -> s == Ill.vlid || s == Ill.shrd, s -> s == Ill.vlid ? Ill.shrd : s),
				// t6
				new BroadcastRule<>(Ill.shrd, Ill.dirt, x -> x == Ill.shrd ? Ill.invd : x),
				// t7
				new LocalRule<>(Ill.shrd, Ill.invd),
				// t8
				new LocalRule<>(Ill.vlid, Ill.invd),
				// t9
				new LocalRule<>(Ill.vlid, Ill.dirt)));
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