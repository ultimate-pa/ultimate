/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.utils;

/**
 * Implements a triple.
 *
 * @param <S> type of the first component 
 * @param <T> type of the second component
 * @param <U> type of the third component
 * 
 * @author Martin
 */
public class Triple<S,T,U> {

	/** First component. */
	private S first;

	/** Second component. */
	private T second;

	/** Third component. */
	private U third;


	/**
	 * Constructs a triple out of three given objects.
	 * 
	 * @param fst first component
	 * @param snd second component
	 * @param thrd third component
	 */
	public Triple(S fst, T snd, U thrd) {
		first = fst;
		second = snd;
		third = thrd;
	}


	/**
	 * Returns the first component of the triple.
	 * 
	 * @return first component of the triple
	 */
	public S getFirst() {
		return first;
	}


	/**
	 * Returns the second component of the triple.
	 * 
	 * @return second component of the triple
	 */
	public T getSecond() {
		return second;
	}


	/**
	 * Returns the third component of the triple.
	 * 
	 * @return third component of the triple
	 */
	public U getThird() {
		return third;
	}
}
