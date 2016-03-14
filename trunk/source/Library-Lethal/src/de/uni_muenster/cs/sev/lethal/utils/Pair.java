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
 * Implements a pair.
 *
 * @param <S> type of the first component 
 * @param <T> type of the second component
 * 
 * @author Martin
 */
public class Pair<S,T> {

	/** First component. */
	private S first;

	
	/** Second component. */
	private T second;


	/**
	 * Constructs a pair out of two given objects.
	 * 
	 * @param fst first component
	 * @param snd second component
	 */
	public Pair(S fst, T snd) {
		first = fst;
		second = snd;
	}


	/**
	 * Returns the first component of the pair.
	 * 
	 * @return the first component of the pair
	 */
	public S getFirst() {
		return first;
	}


	/**
	 * Returns the second component of the pair.
	 * 
	 * @return the second component of the pair
	 */
	public T getSecond() {
		return second;
	}


	/**
	 * Sets the first component of the pair.
	 * 
	 * @param fst the first component of the pair
	 */	
	public void setFirst(S fst){
		this.first = fst;
	}


	/**
	 * Sets the second component of the pair.
	 * 
	 * @param sec the first component of the pair
	 */
	public void setSecond(T sec){
		this.second = sec;
	}


	/**
	 * Computes the hash code of the pair.
	 * 
	 * @return hash code of the pair
	 */
	@Override
	public int hashCode(){
		int hashCode = 31        + (this.first  == null ? 0 : this.first.hashCode());
		hashCode = 31 * hashCode + (this.second == null ? 0 : this.second.hashCode());
		return hashCode;
	}


	/**
	 * Two pairs are equal, if their components are equal.
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj){
		if (obj == null) return false;
		if (!(obj instanceof Pair)) return false;
		if (this.first == null && this.second == null){
			return ((Pair<S, T>)obj).getFirst() == null && ((Pair<S, T>)obj).getSecond() == null;
		} else if (this.first == null){
			return ((Pair<S, T>)obj).getFirst() == null && this.second.equals(((Pair<S, T>)obj).getSecond());
		} else if (this.second == null){
			return ((Pair<S, T>)obj).getSecond() == null && this.first.equals(((Pair<S, T>)obj).getFirst());
		} else {
			return this.first.equals(((Pair<S, T>)obj).getFirst()) && this.second.equals(((Pair<S, T>)obj).getSecond());
		}
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "("+getFirst()+","+getSecond()+")";
	}

}
