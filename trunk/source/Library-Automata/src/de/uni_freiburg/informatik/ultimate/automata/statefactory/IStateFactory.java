/*
 * Copyright (C) 2012-2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.statefactory;

/**
 * In this automata library, we do not have dedicated objects to represent
 * the states of automata (resp. places of Petri nets). 
 * The type of the state is a generic parameter of the automaton class; the
 * user of the library can take the type that is most suitable for his 
 * application.
 * E.g., the AutomataScript interpreter which reads automata from a text file
 * uses string objects as states.  The software verifier Ultimate Automizer
 * uses a class that defines a set of program valuations.
 * 
 * This modular approach requires that new application domains bring their
 * methods for composing states. E.g., in the default string-based application
 * domain the product state of a state "q1" and a state "p7" is the state
 * that is represented by the composed string "(q1,p7)".  The software verifier
 * uses some conjunction-like operation for predicates to obtain the object
 * that represents the product state.
 * 
 * We encapsulate the construction of states via the {@link IStateFactory}
 * interfaces. Developers of automata operations have to define new interfaces
 * or use existing interfaces for constructing states. Users of the automata 
 * library that use a new application domain have to implement these interfaces.
 * 
 * This is an empty interface only used to mark other state factories. Every factory for states used in the automata
 * library must implement this empty interface. The purpose is to allow the automata script interpreter to identify a
 * constructor argument as a state factory and pass a {@link StringFactory}.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public interface IStateFactory<STATE> {

}
