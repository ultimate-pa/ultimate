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
package pea;

import java.util.Set;


public class EventDecision extends Decision {
    String event;

    public EventDecision(String ev) {
        event = ev;
    }

    /**
     * Create a new constraint specifying that all must events are in the set
     * and all forbid events aren't.
     */
    public static CDD create(Set<String> must, Set<String> forbid) {
        CDD result = CDD.TRUE;

        for (String evt : must)
            result = result.and(create(evt));

        for (String evt : forbid)
            result = result.and(create('/', evt));

        return result;
    }

    /**
     * Create an event atom specifying that an event is forbidden.
     *
     * @param forbidden
     *            ignored, should be '/'.
     * @param event
     *            the event that is forbidden.
     */
    public static CDD create(char forbidden, String event) {
        return CDD.create(new EventDecision(event), CDD.falseChilds);
    }

    /**
     * Create an event atom specifying that an event must occur.
     *
     * @param event
     *            the event that must occur.
     */
    public static CDD create(String event) {
        return CDD.create(new EventDecision(event), CDD.trueChilds);
    }

    public boolean equals(Object o) {
        if (!(o instanceof EventDecision)) {
            return false;
        }

        if (!event.equals(((EventDecision) o).event)) {
            return false;
        }

        return true;
    }

    public int hashCode() {
        return event.hashCode();
    }

    public int compareTo(Object o) {
        if (!(o instanceof EventDecision)) {
            return -1;
        }

        return event.compareTo(((EventDecision) o).event);
    }

    public String toString(int child) {
        return (child == 0) ? event : ("/" + event);
    }

    public String toSmtString(int child) {
        return toString(child);
    }

    public String toUppaalString(int child) {
        return "true";
    }

    public String toUppaalStringDOM(int child) {
        return "true";
    }

    /**
     * @return Returns the event.
     */
    public String getEvent() {
        return event;
    }

    @Override
    public Decision prime() {
        return this;
    }

    @Override
    public Decision unprime() {
        return this;
    }

    @Override
    public String toTexString(int child) {
        return (child == 0) ? event : ("\\neg" + event);
    }

    public String getVar() {
        return "";
    }
}
