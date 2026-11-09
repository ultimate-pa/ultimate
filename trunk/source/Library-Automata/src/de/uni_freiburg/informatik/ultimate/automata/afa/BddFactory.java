/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 Ecole Polytechnique
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.function.Function;
import java.util.stream.Collector;

/**
 * Used for construction of BDDs representing boolean formulas over a given type of variables.
 *
 * @param <V>
 *            the type of variables
 */
public class BddFactory<V> {
	private final BddManager mManager;
	private final IBddSignature<V> mSignature;

	public BddFactory(final BddManager manager, final IBddSignature<V> signature) {
		mManager = manager;
		mSignature = signature;
	}

	public static <V> BddFactory<V> create() {
		final var manager = new BddManager();
		return new BddFactory<>(manager, new SimpleBddSignature<>(manager));
	}

	public Bdd variable(final V variable) {
		return mManager.variable(mSignature.getVariableIndex(variable));
	}

	public Bdd getTrue() {
		return mManager.getTrue();
	}

	public Bdd getFalse() {
		return mManager.getFalse();
	}

	public Collector<Bdd, ?, Bdd> toConjunction() {
		return Collector.of(mManager::getTrue, mManager::and, mManager::and);
	}

	public Collector<Bdd, ?, Bdd> toDisjunction() {
		return Collector.of(mManager::getFalse, mManager::or, mManager::or);
	}

	public <W> BddFactory<W> withRenaming(final Function<W, V> renamer) {
		return new BddFactory<>(mManager, new RenamingBddSignature<>(mSignature, renamer));
	}
}
