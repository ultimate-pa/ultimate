/*
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.Set;

public class EventDecision extends Decision<EventDecision> {

	private final String mEvent;

	public EventDecision(final String ev) {
		mEvent = ev;
	}

	/**
	 * Create a new constraint specifying that all must events are in the set and all forbid events aren't.
	 */
	public static CDD create(final Set<String> must, final Set<String> forbid) {
		CDD result = CDD.TRUE;

		for (final String evt : must) {
			result = result.and(create(evt));
		}

		for (final String evt : forbid) {
			result = result.and(createNeg(evt));
		}

		return result;
	}

	/**
	 * Create an event atom specifying that an event is forbidden.
	 *
	 * @param event
	 *            the event that is forbidden.
	 */
	public static CDD createNeg(final String event) {
		return CDD.create(new EventDecision(event), CDD.FALSE_CHILDS);
	}

	/**
	 * Create an event atom specifying that an event must occur.
	 *
	 * @param event
	 *            the event that must occur.
	 */
	public static CDD create(final String event) {
		return CDD.create(new EventDecision(event), CDD.TRUE_CHILDS);
	}

	@Override
	public boolean equals(final Object o) {
		if (o == null || o.getClass() != getClass()) {
			return false;
		}

		return mEvent.equals(((EventDecision) o).mEvent);
	}

	@Override
	public int hashCode() {
		return mEvent.hashCode();
	}

	@Override
	public String toString(final int child) {
		return (child == 0) ? mEvent : ("/" + mEvent);
	}

	@Override
	public String toSmtString(final int child) {
		return toString(child);
	}

	@Override
	public String toUppaalString(final int child) {
		return "true";
	}

	@Override
	public String toUppaalStringDOM(final int child) {
		return "true";
	}

	/**
	 * @return Returns the event.
	 */
	public String getEvent() {
		return mEvent;
	}

	@Override
	public EventDecision prime() {
		return this;
	}

	@Override
	public EventDecision unprime() {
		return this;
	}

	@Override
	public EventDecision prime(final String ignore) {
		return this;
	}

	@Override
	public EventDecision unprime(final String ignore) {
		return this;
	}

	@Override
	public String toTexString(final int child) {
		return (child == 0) ? mEvent : ("\\neg" + mEvent);
	}

	@Override
	public String getVar() {
		return "";
	}

	@Override
	public int compareToSimilar(final Decision<?> other) {
		return mEvent.compareTo(((EventDecision) other).mEvent);
	}
}
