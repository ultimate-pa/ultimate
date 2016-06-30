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
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.grammars;

import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.InnerSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.LeafSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;

/**
 * Implements the construction of a regular tree grammar out of a finite tree automaton.
 * 
 * @see FTA
 * @see RTG
 *
 * @author Martin, Sezar
 */
public class RTGOps {



	/**
	 * Given a finite tree automaton, constructs an equivalent regular tree grammar.
	 * 
	 * @param <Q> type of the states occurring in the given finite tree automaton
	 * @param <F> type of the ranked symbols occurring in the given finite tree automaton
	 * @param fta finite tree automaton that is be converted in an equivalent regular tree grammar
	 * @return regular tree grammar that is equivalent to the given finite tree automaton
	 */
	public static <F extends RankedSymbol,Q extends State>
	RTG<F,Q> makeGrammarFromFTA(FTA<F,Q,? extends FTARule<F,Q>> fta) {
		// the start symbols are just the final states of the given finite tre automaton
		final Set<Q> start = new HashSet<Q>(fta.getFinalStates());
		// each rule of the automaton is converted into grammar rule
		final Set<RTGRule<F,Q>> newRules = new HashSet<RTGRule<F,Q>>();
		for (final FTARule<F,Q> rule: fta.getRules()) {
			// convert left side of teh automaton rule into a tree
			final List<Tree<BiSymbol<F,Q>>> rightSideSubTrees = new LinkedList<Tree<BiSymbol<F,Q>>>();
			for (Q qsrc: rule.getSrcStates()) {
				BiSymbol<F,Q> newRoot = new LeafSymbol<F,Q>(qsrc);
				rightSideSubTrees.add(TreeFactory.getTreeFactory().makeTreeFromSymbol(newRoot));
			}
			final Tree<BiSymbol<F,Q>> rightSideTree = TreeFactory.getTreeFactory().makeTreeFromSymbol(new InnerSymbol<F,Q>(rule.getSymbol()), rightSideSubTrees);
			// changing left and right side of the automaton rule makes the new grammr rule
			RTGRule<F,Q> newRule = new RTGRule<F,Q>() {
				@Override
				public Q getLeftSide() {
					return rule.getDestState();
				}

				@Override
				public Tree<BiSymbol<F, Q>> getRightSide() {
					return rightSideTree;
				}

			};
			newRules.add(newRule);
		}
		// new grammar with these start symbols and rules
		return new RTG<F,Q>() {
			@Override
			public Set<RTGRule<F, Q>> getGrammarRules() {
				return newRules;
			}

			@Override
			public Set<Q> getStartSymbols() {
				return start;
			}

		};
	}


}
