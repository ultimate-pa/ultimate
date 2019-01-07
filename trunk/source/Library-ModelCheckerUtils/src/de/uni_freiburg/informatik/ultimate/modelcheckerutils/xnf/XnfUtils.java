/*
 * Copyright (C) 2015 David Zschocke
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015-2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2015-2017 University of Freiburg
 *
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.xnf;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;


/**
 * TODO 2019-01-06: fix documentation of this class' methods
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class XnfUtils {

	private XnfUtils() {
		// do not instantiate
	}



	/**
	 * Given two disjunctions a and b of conjunctions, this method calculates a new disjunction of conjunctions
	 * equivalent to a /\ b
	 *
	 * @param a
	 *            the first dnf
	 * @param b
	 *            the second dnf
	 * @param <E>
	 *            the type of the literals in the dnf
	 * @return a new dnf equivalent to a /\ b
	 */
	static <E> Dnf<E> expandConjunctionSingle(final Dnf<E> a, final Dnf<E> b) {
		final Dnf<E> result = new Dnf<>();
		for (final Collection<E> aItem : a) {
			for (final Collection<E> bItem : b) {
				final Collection<E> resultItem = new ArrayList<>();
				resultItem.addAll(aItem);
				resultItem.addAll(bItem);
				result.add(resultItem);
			}
		}
		return result;
	}

	/**
	 * Given a set of {@link DNF}s, construct a {@link DNF} that represent the conjunction of the input {@link DNF}s.
	 *
	 * @param <E>
	 *            the type of the literals in the dnfs
	 * @return DNF representing the conjunction of the DNFs provided, returns NULL if no DNFs were given.
	 */
	@SafeVarargs
	public static <E> Dnf<E> and(final IUltimateServiceProvider services, final Dnf<E>... dnfs) {
		boolean firstElement = true;
		Dnf<E> expandedDnf = null;
		for (final Dnf<E> currentDnf : dnfs) {
			if (!services.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(XnfUtils.class,
						"transforming conjunction of length " + dnfs.length + " to DNF");
			}
			if (firstElement) {
				expandedDnf = currentDnf;
				firstElement = false;
			} else {
				expandedDnf = expandConjunctionSingle(currentDnf, expandedDnf);
			}
		}
		return expandedDnf;
	}

	/**
	 * Transforms a cnf (given as two nested Collections of atoms (usually linear inequalites)) into dnf (given as two
	 * nested Collections of atoms (usually linear inequalites)).
	 *
	 * @param <E>
	 *            type of the atoms
	 *
	 * @param cnf
	 *            the collection of conjuncts consisting of disjuncts of linear inequalities
	 * @return a dnf (Collection of disjuncts consisting of conjuncts of linear inequalities), equivalent to the given
	 *         cnf
	 */
	static <E> Dnf<E> expandCnfToDnf(final IUltimateServiceProvider services, final Cnf<E> cnf) {
		if (cnf.isEmpty()) {
			final Collection<E> empty = Collections.emptyList();
			return new Dnf<>(empty);
		}
		boolean firstElement = true;
		Dnf<E> expandedDnf = null;
		for (final Collection<E> conjunct : cnf) {
			if (!services.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(XnfUtils.class,
						"transforming CNF with " + cnf.size() + "conjuncts to DNF");
			}
			if (firstElement) {
				expandedDnf = new Dnf<>();
				for (final E e : conjunct) {
					final Collection<E> conjunctSingleton = new ArrayList<>();
					conjunctSingleton.add(e);
					expandedDnf.add(conjunctSingleton);
				}
				firstElement = false;
			} else {
				expandedDnf = expandCnfToDnfSingle(services, expandedDnf, conjunct);
			}
		}
		assert expandedDnf != null;
		return expandedDnf;
	}

	/**
	 * Performs a single expandation, meaning transforming conjunct /\ dnf to an equivalent dnf
	 *
	 * @param dnf
	 *            the dnf the conjunct is conjuncted to
	 * @param conjunct
	 *            the conjunct that is conjuncted to the dnf
	 * @param <E>
	 *            : the type of Literals in the cnf/dnf
	 * @return a new dnf equivalent to conjunct /\ dnf
	 */
	static <E> Dnf<E> expandCnfToDnfSingle(final IUltimateServiceProvider services, final Dnf<E> dnf,
			final Collection<E> conjunct) {
		final Dnf<E> result = new Dnf<>();
		for (final Collection<E> disjunct : dnf) {
			for (final E item : conjunct) {
				if (!services.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(XnfUtils.class,
							"transforming CNF to DNF");
				}
				final Collection<E> resultItem = new ArrayList<>();
				resultItem.addAll(disjunct);
				resultItem.add(item);
				result.add(resultItem);
			}
		}
		return result;

	}

}
