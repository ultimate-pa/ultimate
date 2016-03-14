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
package de.uni_muenster.cs.sev.lethal.hedgeautomaton;

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.*;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.*;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;

import java.util.*;

/**
 * Hedge automaton class. It contains transformation algorithms, which is done very
 * lazy.
 *
 * @author Anton, Maria
 * @param <G_Symbol>
 * symbol type of hedge automaton
 * @param <G_State>
 * state type of hedge automaton
 */
public class HedgeAutomaton<G_Symbol extends UnrankedSymbol, G_State extends State> {
	private final static boolean DEBUG = false;
	private final static boolean DEBUG_HA = false;

	private Set<G_State> states; // States of the hedge automaton
	private Set<G_State> finalStates; // Final states of the hedge automaton
	private Set<HedgeRule<G_Symbol, G_State>> rules; // Rules of the hedge
	// automaton
	private final StateFactory sF = StateFactory.getStateFactory();
	// private final Namespace namespace; // factories for this hedge automaton
	private FTA<HedgeSymbol<G_Symbol>,
			HedgeState<G_State>,
			? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TA; // Transformed
	// automaton

	/**
	 * Constructor for the hedge automaton.
	 *
	 * @param States			States of the hedge automaton
	 * @param FinalStates Final states of the hedge automaton
	 * @param Rules			 Rules of the hedge automaton
	 */
	public HedgeAutomaton(final Set<G_State> States,
												final Set<G_State> FinalStates,
												final Set<HedgeRule<G_Symbol, G_State>> Rules) {
		super();
		this.states = States;
		this.finalStates = FinalStates;
		this.rules = Rules;
		this.TA = null;
	}

	/**
	 * Constructor for the hedge automaton from hedge automaton transformed as
	 * tree automaton.
	 *
	 * @param TA hedge automaton transformed as tree automaton
	 */
	protected HedgeAutomaton(
			final FTA<HedgeSymbol<G_Symbol>,
					HedgeState<G_State>,
					? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TA) {
		super();
		this.states = null;
		this.finalStates = null;
		this.rules = null;
		this.TA = clean(TA);
	}

	/**
	 * Transforms the hedge automaton into a tree automaton.
	 */
	private void HA2TA() {
		if (DEBUG)
			System.out.println("<-- BEGIN: HedgeAutomaton.HA2TA -->");
		// Set of states for TA
		//final Set<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		// Set of rules for TA
		final Set<FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		// the cons and nil
		final HedgeSymbol<G_Symbol> sNil = HedgeSymbolCache.getNilSymbol(this);
//		final HedgeSymbol<G_Symbol> sCons = HedgeSymbolCache.getConsSymbol(this);

		LinkedList<HedgeState<G_State>> tempStates = new LinkedList<HedgeState<G_State>>();

		// create the state which indicates an recognised Nil symbol:
		final HedgeState<G_State> firstState = new HedgeState<G_State>(null, sF
				.makeState());
		FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> firstRule = new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(
				sNil, tempStates, firstState);
		if (DEBUG)
			System.out.println("<-- HedgeAutomaton.HA2TA created rule " + sNil
					+ "(" + tempStates + ") -> " + firstState + " -->");
		//TAStates.add(firstState);
		TARules.add(firstRule);

		// collection with the initializers and finalizers
		final Collection<Init<G_Symbol, G_State>> inits = new HashSet<Init<G_Symbol, G_State>>();
		final Collection<Finit<G_Symbol, G_State>> finits = new HashSet<Finit<G_Symbol, G_State>>();

		for (final HedgeRule<G_Symbol, G_State> rule : this.rules) {

			// collect the initializer, execute if new
			final Init<G_Symbol, G_State> init = rule.getExpression()
					.getInitializer();
			if (init != null && !inits.contains(init)) {
				inits.add(init);
				init.initialize(this);
			}

			// collect the finalizer
			final Finit<G_Symbol, G_State> finit = rule.getExpression()
					.getFinaliser();
			if (finit != null && !finits.contains(finit))
				finits.add(finit);
			if (DEBUG)
				System.out
						.println("<-- HedgeAutomaton.HA2TA call cache.transformExp("
								+ rule + ") -->");

			final Container<G_Symbol, G_State> result;

			// the firstState shall recognize the Nil symbol only. So create new
			// state if we cannot guarantee it
			// get tranformed expression as FTA
			if (rule.getExpression().acceptsEmptyWord()) {
				final HedgeState<G_State> firstState_2 = new HedgeState<G_State>(
						null, sF.makeState());
				tempStates = new LinkedList<HedgeState<G_State>>();
				firstRule = new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(
						sNil, tempStates, firstState_2);
				//TAStates.add(firstState_2);
				TARules.add(firstRule);
				result = rule.getExpression().transform(firstState_2, this,
						this.sF);
			} else
				result = rule.getExpression().transform(firstState, this,
						this.sF);
			if (DEBUG)
				System.out
						.println("<-- HedgeAutomaton.HA2TA call returned -->");

			// collect all the states and rules from transformed expression
			//TAStates.addAll(result.getStates());
			TARules.addAll(result.getRules());
			if (DEBUG)
				System.out
						.println("<-- HedgeAutomaton.HA2TA create final tree rules for the hedge rules -->");

			// create a rule with user symbol which accepts the endstates of the
			// transformed expression
			for (final HedgeState<G_State> endState : result.getFinalStates()) {
				tempStates = new LinkedList<HedgeState<G_State>>();
				tempStates.add(endState);
				firstRule = new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(
						HedgeSymbolCache.getSymbol(rule.getSymbol()),
						tempStates, HedgeStateCache.getState(rule.getState()));
				if (DEBUG)
					System.out.println("<-- HedgeAutomaton.HA2TA created rule "
							+ firstRule.getSymbol() + "("
							+ firstRule.getSrcStates() + ") -> "
							+ firstRule.getDestState());
				TARules.add(firstRule);
			}
		}
		if (DEBUG)
			System.out.println("<-- HedgeAutomaton.HA2TA got " + finits.size()
					+ " cleanings to do...");

		// execute all finalizers
		for (final Finit<G_Symbol, G_State> fin : finits)
			fin.finalize(this);

		// the endstates of the generated FTA are the tranformed endstates of
		// the HA.
		final Collection<HedgeState<G_State>> finalStates = new HashSet<HedgeState<G_State>>();
		for (final G_State state : this.finalStates)
			finalStates.add(HedgeStateCache.getState(state));
		if (DEBUG)
			System.out.println("<-- END: HedgeAutomaton.HA2TA -->");
		// create FTA
		this.TA = new GenFTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(
				TARules, finalStates);
		// ensure the cons symbol is included in the alphabet. This is necessary
		// for generation of complement and determination.
//		TA.addSymbol(sCons);
	}

	/**
	 * Inner class which is used for representation of a tree automaton as a graph.
	 *
	 * @param <G_State>
	 * state type
	 * @param <G_Symbol>
	 * symbol type
	 */
	static class GraphNode<G_Symbol extends UnrankedSymbol, G_State extends State> {
		// incoming and outgoing edges with expressions used to move through the
		// edges
		HashMap<GraphNode<G_Symbol, G_State>, RegularExpression<G_Symbol, G_State>> in2,
				out2;
		// edges which loops to this node
		RegularExpression<G_Symbol, G_State> loop2;

		// separated nodes and their expressions. order is retained.
		List<GraphNode<G_Symbol, G_State>> graph_list;
		List<RegularExpression<G_Symbol, G_State>> expr_list;

		// if this node is needed for the generated FTA. otherwise it will be
		// deleted completely
		boolean needed;
		// used to create incoming edges. indicates if the outgoing nodes are
		// informed of my edges to them.
		boolean generated;
		RegularExpression<G_Symbol, G_State> expression;

		GraphNode() {
			super();
			this.in2 = new HashMap<GraphNode<G_Symbol, G_State>, RegularExpression<G_Symbol, G_State>>();
			this.out2 = new HashMap<GraphNode<G_Symbol, G_State>, RegularExpression<G_Symbol, G_State>>();
			this.loop2 = null;
			this.generated = false;
			this.needed = false;
			this.expression = null;
		}

		/**
		 * Tells this node it's needed for the generated FTA.
		 */
		public void setNeeded() {
			if (DEBUG_HA)
				System.out.println(this + " is needed");
			this.needed = true;
		}

		/**
		 * Adds new edge to a node with the given state as input.
		 *
		 * @param node	node the edge is pointing to
		 * @param state input for the edge
		 */
		public void addOut(final GraphNode<G_Symbol, G_State> node,
											 final HedgeState<G_State> state) {
			if (DEBUG_HA)
				System.out.println("adding link from " + this + " to " + node
						+ " with " + state);
			final List<G_State> l = new LinkedList<G_State>();
			l.add(state.getOriginal());
			final RegularExpression<G_Symbol, G_State> exp = new Expression<G_Symbol, G_State>(
					1, 1, new BasicExpression<G_Symbol, G_State>(l));
			// if the node the edge is refering to is me, the edge is a looping
			// edge
			if (node == this) {
				if (DEBUG_HA)
					System.out.println("its a loop");
				// add the expression to the loops
				addLoop(exp);
				return;
			}
			// otherwise add it to the outgoing nodes
			if (DEBUG_HA)
				System.out.println("its not a loop");
			addOut(node, exp);
		}

		/**
		 * Used for generation of incoming edges. Gets the information about an
		 * node with an edge to me. Informs all nodes the outgoing edges pointing
		 * at of the edge to them.
		 *
		 * @param node the node which has an edge to me. is null for starting
		 *             recursion.
		 * @param exp	the input-expression for the edge to me. may be null if
		 *             node is null.
		 */
		public void processGraph(final GraphNode<G_Symbol, G_State> node,
														 final RegularExpression<G_Symbol, G_State> exp) {
			if (DEBUG_HA)
				System.out.println("genarating incoming nodes for " + this);
			// if the node with the expression are set, add them as incoming
			// edge
			if (node != null) {
				assert exp != null;
				if (DEBUG_HA)
					System.out.println("checking incoming node " + node);
				addIn(node, exp);
			}
			// if the recursion was done before, don't do it again!
			if (this.generated)
				return;
			if (DEBUG_HA)
				System.out.println("outgoing nodes are not yet informed of me");
			// save that the recursion was done before.
			this.generated = true;
			// inform the nodes the outgoing edges are poiting at about my edge
			// to them
			for (final GraphNode<G_Symbol, G_State> keyNode : out2.keySet()) {
				keyNode.processGraph(this, out2.get(keyNode));
			}
			if (DEBUG_HA)
				System.out.println("node " + this + " is done");
		}

		/**
		 * Adds the node with its edge to me to the incoming edges.
		 *
		 * @param node the node with an edge pointing at me
		 * @param exp	the input-expression for the edge to me
		 */
		void addIn(final GraphNode<G_Symbol, G_State> node,
							 RegularExpression<G_Symbol, G_State> exp) {
			if (in2.containsKey(node)) {
				exp = OrExpression.makeOptimizedOr(1, 1, in2.get(node), exp);
			}
			in2.put(node, exp);
		}

		/**
		 * Adds the node with its edge to me to the outgoing edges.
		 *
		 * @param node the node the edge is pointing at
		 * @param exp	the input-expression for the edge
		 */
		void addOut(final GraphNode<G_Symbol, G_State> node,
								RegularExpression<G_Symbol, G_State> exp) {
			if (out2.containsKey(node)) {
				exp = OrExpression.makeOptimizedOr(1, 1, out2.get(node), exp);
			}
			out2.put(node, exp);
		}

		/**
		 * Adds an looping edge.
		 *
		 * @param exp the input-expression for the edge
		 */
		void addLoop(RegularExpression<G_Symbol, G_State> exp) {
			if (this.loop2 != null) {
				exp = OrExpression.makeOptimizedOr(1, 1, this.loop2, exp);
			}
			this.loop2 = exp;
		}

		/**
		 * 1. Deletes the edge to node 'node' if 'delete' is true <br> 2. Creates new
		 * edges to nodes 'newNodes' the input consists of: - 'input' -
		 * Expression in 'expr' on same position as the node, this edge pointing
		 * at, in newNodes.
		 *
		 * @param node		 the node to delete the edge to
		 * @param input		first part of the input for new edges
		 * @param newNodes list of the nodes, to create new edges to
		 * @param expr		 list of second parts for the input, one for each node
		 * @param delete	 if the old edge shall be deleted
		 */
		public void exchangeOutgoing(final GraphNode<G_Symbol, G_State> node,
																 final RegularExpression<G_Symbol, G_State> input,
																 final Collection<GraphNode<G_Symbol, G_State>> newNodes,
																 final List<RegularExpression<G_Symbol, G_State>> expr,
																 final boolean delete) {
			// if processGraph does correctly, out has the node
			assert out2.containsKey(node);
			// if delete works correctly, newNodes and expr are of equal length
			assert newNodes.size() == expr.size();

			// 1. deletes the edge to node 'node'
			if (delete)
				out2.remove(node);

			// 2. create simultaneous move through the two lists
			final Iterator<RegularExpression<G_Symbol, G_State>> expr_I = expr
					.iterator();
			for (final GraphNode<G_Symbol, G_State> for_node : newNodes) {
				RegularExpression<G_Symbol, G_State> for_exp = expr_I.next();

				// concatenate the first part to the second one:
				for_exp = ConcatExpression.makeOptimizedConcat(1, 1, input,
						for_exp);

				// if the new edge is pointing from this node to same, its a
				// loop ;)
				if (for_node == this) {
					addLoop(for_exp);
					continue;
				}

				// if the new edge is not a loop:
				// add an edge to the node and notify it about new incoming node
				addOut(for_node, for_exp);
				for_node.addIn(this, for_exp);
			}
		}

		/**
		 * 'Deletes' the node from the graph by: - all nodes pointing to this
		 * one (incoming nodes) get new edges to nodes this one pointing at
		 * (using 'exchange'). - The set of incoming nodes is deleted. - The
		 * nodes this one is pointing at (outgoing nodes) are asked to delete
		 * this one from the set of incoming nodes, if this one is not a
		 * starting node.
		 */
		public void delete() {
			if (DEBUG_HA)
				System.out.println("deletion of " + this);
			// if this node is first or last one, do not delete it.
			if (out2.isEmpty() || in2.isEmpty())
				return;
			if (DEBUG_HA)
				System.out.println("start");

			this.graph_list = new LinkedList<GraphNode<G_Symbol, G_State>>();
			this.expr_list = new LinkedList<RegularExpression<G_Symbol, G_State>>();

			// create the lists for 'exchangeOutgoing' (second part of
			// expressions) from the outgoing nodes
			// and ask to delete this one from the set of incoming nodes, if
			// this one is not a starting node.
			for (final GraphNode<G_Symbol, G_State> node : out2.keySet()) {
				graph_list.add(node);
				expr_list.add(out2.get(node));
				node.deleteIn(this);
			}
			out2.clear();
			this.out2 = null;

			// create a loop from loop expression
			if (this.loop2 != null) {
				this.loop2 = new Expression<G_Symbol, G_State>(0, -1, loop2
						.getExpression());
			}

			// calling 'exchangeOutgoing' on every incoming node
			for (final GraphNode<G_Symbol, G_State> node : in2.keySet()) {
				RegularExpression<G_Symbol, G_State> exp = in2.get(node);
				if (this.loop2 != null)
					exp = ConcatExpression.makeOptimizedConcat(1, 1, exp,
							this.loop2);
				node.exchangeOutgoing(this, exp, this.graph_list,
						this.expr_list, !this.needed);
			}

			// the set of incoming nodes is deleted.
			if (!this.needed) {
				in2.clear();
				this.in2 = null;
			}
			if (DEBUG_HA)
				System.out.println("deletion of " + this + " complete");
		}

		public void deleteIn(final GraphNode<G_Symbol, G_State> node) {
			// if delete works correctly, the node is an incoming node
			assert in2.containsKey(node);
			in2.remove(node);
		}

		/**
		 * Makes an infinite loop from the looping edges and returns it.
		 *
		 * @return expression with the infinite loop from the looping edges
		 */
		RegularExpression<G_Symbol, G_State> getLoop() {
			if (this.loop2 != null) {
				this.loop2 = new Expression<G_Symbol, G_State>(0, -1, loop2
						.getExpression());
			}
			return this.loop2;
		}

		/**
		 * Generates the expression this node identifies by collecting the
		 * expressions from incoming edges and nodes they come from.
		 *
		 * @return the expression this node identifies by collecting the
		 *         expressions from incoming edges and nodes they come from
		 */
		public RegularExpression<G_Symbol, G_State> getExpression() {
			// if the expression was already gererated, just return it
			if (this.expression != null)
				return this.expression;

			if (DEBUG_HA)
				System.out.println("start exp for node " + this);
			// one part is the loop
			this.expression = getLoop();
			if (DEBUG_HA)
				System.out.println("loop: " + this.expression);

			// the other part is the expression before me, identified by
			// incoming edges
			RegularExpression<G_Symbol, G_State> secondPart = null;
			final Iterator<GraphNode<G_Symbol, G_State>> it = in2.keySet()
					.iterator();
			if (it.hasNext()) {
				GraphNode<G_Symbol, G_State> for_node = it.next();
				secondPart = for_node.getExpression();
				// collect the expresion the first incoming edge identifies
				if (secondPart.isEmpty())
					secondPart = in2.get(for_node);
				else
					secondPart = ConcatExpression.makeOptimizedConcat(1, 1,
							secondPart, in2.get(for_node));

				if (DEBUG_HA)
					System.out.println("incoming: " + secondPart);
				// collect the expresion the the other incoming edges identify
				for (; it.hasNext();) {
					for_node = it.next();
					RegularExpression<G_Symbol, G_State> newExp = for_node
							.getExpression();
					if (newExp.isEmpty())
						newExp = in2.get(for_node);
					else
						newExp = ConcatExpression.makeOptimizedConcat(1, 1,
								newExp, in2.get(for_node));
					secondPart = OrExpression.makeOptimizedOr(1, 1, secondPart,
							newExp);
					if (DEBUG_HA)
						System.out.println("incoming: " + secondPart);
				}
			}
			if (DEBUG_HA)
				System.out.println("expression: " + this.expression);
			if (DEBUG_HA)
				System.out.println("secondPart: " + secondPart);

			// the expression i identify is the concat of the expresion before
			// me and the loops in me
			if (this.expression == null || this.expression.isEmpty()) {
				if (DEBUG_HA)
					System.out.println("1.0");
				if (secondPart == null) {
					if (DEBUG_HA)
						System.out.println("1.1");
					this.expression = new EmptyExpression<G_Symbol, G_State>();
				} else {
					if (DEBUG_HA)
						System.out.println("1.2");
					this.expression = secondPart;
				}
			} else {
				if (DEBUG_HA)
					System.out.println("2.0");
				if (secondPart != null && !secondPart.isEmpty()) {
					if (DEBUG_HA)
						System.out.println("2.1");
					this.expression = ConcatExpression.makeOptimizedConcat(1,
							1, secondPart, this.expression);
				}
			}
			if (DEBUG_HA)
				System.out.println(this + " == " + this.expression);
			return this.expression;
		}

		/**
		 * String representation of me. displays incoming edges, the loops and
		 * the outgoing edges.
		 *
		 * @return string representation of the node
		 */
		public String getString() {
			final StringBuilder buffer = new StringBuilder();
			buffer.append("in:\n");
			if (this.in2 != null)
				for (final GraphNode<G_Symbol, G_State> node : in2.keySet()) {
					buffer.append(node).append(" => ").append(in2.get(node));
				}
			buffer.append("\nloop:\n").append(this.loop2).append("\nout:\n");
			if (this.out2 != null)
				for (final GraphNode<G_Symbol, G_State> node : out2.keySet()) {
					buffer.append(node).append(" => ").append(out2.get(node));
				}
			buffer.append("\n");
			return buffer.toString();
		}
	}

	/**
	 * Reconstructs the hedge automaton from the tree automaton representation.
	 */
	private void TA2HA() {
		assert this.TA != null;

		final HashMap<HedgeState<G_State>, GraphNode<G_Symbol, G_State>> nodes = new HashMap<HedgeState<G_State>, GraphNode<G_Symbol, G_State>>();
		final Collection<HedgeState<G_State>> nilRules = new HashSet<HedgeState<G_State>>();
		Set<FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> userRules = new HashSet<FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		final Collection<HedgeState<G_State>> userStates = new HashSet<HedgeState<G_State>>();

		// sort the rules into 3 groups:
		if (DEBUG_HA)
			System.out.println("go through rules");
		for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : TA
				.getRules()) {
			if (DEBUG_HA)
				System.out.println(rule);
			if (DEBUG_HA)
				System.out.println(rule.getDestState());
			final List<HedgeState<G_State>> input = rule.getSrcStates();
			switch (input.size()) {
				// the rules with nil as symbol
				case 0:
					if (DEBUG_HA)
						System.out.println("is Nil");
					// all rules with no input are nil rules
					assert rule.getSymbol().equals(
							HedgeSymbolCache.getNilSymbol(this));

					nilRules.add(rule.getDestState());
					break;
				// the rules with user symbols
				case 1:
					if (DEBUG_HA)
						System.out.println("is user");
					userRules.add(rule);
					userStates.add(rule.getDestState());
					if (DEBUG_HA)
						System.out.println("user rules:\n" + userRules);
					break;
				// the rules with cons as symbol
				case 2:
					if (DEBUG_HA)
						System.out.println("is Cons");
					// all rules with 2 input states are cons rules
					assert rule.getSymbol().equals(
							HedgeSymbolCache.getConsSymbol(this));

					final GraphNode<G_Symbol, G_State> node;
					final Iterator<HedgeState<G_State>> inputI = input.iterator();
					final HedgeState<G_State> in1 = inputI.next();
					final HedgeState<G_State> in2 = inputI.next();
					if (DEBUG_HA)
						System.out.println("State1: " + in1 + " State2: " + in2);
					// creates the graphnodes from the cons rules
					// this generates the graph over all the cons rules which
					// contains all
					// the information about the states the FTA goes through from
					// the nil
					// symbol to the user Symbol on top. this allows us to use the
					// elemination
					// algorithm quite efficiently.
					if (nodes.containsKey(in1)) {
						if (DEBUG_HA)
							System.out.println(in1 + " is already present");
						node = nodes.get(in1);
					} else {
						if (DEBUG_HA)
							System.out.println(in1 + " is new");
						node = new GraphNode<G_Symbol, G_State>();
						nodes.put(in1, node);
						if (DEBUG_HA)
							System.out.println("nodes after insert: " + nodes);
					}
					final GraphNode<G_Symbol, G_State> node2;
					final HedgeState<G_State> dest = rule.getDestState();
					if (nodes.containsKey(dest)) {
						if (DEBUG_HA)
							System.out.println(dest + " is already present");
						node2 = nodes.get(dest);
					} else {
						if (DEBUG_HA)
							System.out.println(dest + " is new");
						node2 = new GraphNode<G_Symbol, G_State>();
						nodes.put(dest, node2);
						if (DEBUG_HA)
							System.out.println("nodes after insert: " + nodes);
					}
					if (DEBUG_HA)
						System.out.println("generation of out for " + node);
					node.addOut(node2, in2);
					break;
				default:
					throw new IllegalArgumentException();
			}
		}
		if (DEBUG_HA)
			System.out.println("go through rules - done.");

		final Set<G_State> myStates = new HashSet<G_State>();
		final Set<HedgeRule<G_Symbol, G_State>> myRules = new HashSet<HedgeRule<G_Symbol, G_State>>();
		// do some more cleaning
		// removing useless user rules:
		final Set<FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> newUserRules = new HashSet<FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		HedgeState<G_State> in;
		final Expression<G_Symbol, G_State> emptyExpression = new EmptyExpression<G_Symbol, G_State>();
		for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : userRules) {
			in = rule.getSrcStates().get(0);
			if (nodes.containsKey(in))
				newUserRules.add(rule);
			else if (nilRules.contains(in)) {
				myRules.add(new HedgeRule<G_Symbol, G_State>(rule.getSymbol()
						.getOriginal(), emptyExpression, rule.getDestState()
						.getOriginal()));
				myStates.add(rule.getDestState().getOriginal());
			} else if (userStates.contains(in)) {
				myRules.add(new HedgeRule<G_Symbol, G_State>(rule.getSymbol()
						.getOriginal(), new Expression<G_Symbol, G_State>(1, 1,
						new BasicExpression<G_Symbol, G_State>(HedgeState
								.extractOriginal(rule.getSrcStates()))), rule
						.getDestState().getOriginal()));
				myStates.add(rule.getDestState().getOriginal());
			}
		}
		userRules = newUserRules;

		// start the recursive generation of incoming edges in the graph
		if (DEBUG_HA)
			System.out.println("generation on incoming nodes:");
		for (final GraphNode<G_Symbol, G_State> node : nodes.values()) {
			if (DEBUG_HA)
				System.out.println("node: " + node);
			node.processGraph(null, null);
		}
		if (DEBUG_HA)
			System.out.println("generation on incoming nodes done.");
		if (DEBUG_HA)
			System.out.println("checking needed nodes:");
		// now we know the nodes we need for the resulting automaton
		// so we tell them they are needed, so the elemination algorithm takes
		// care of them
		Iterator<HedgeState<G_State>> inputI;
		for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : userRules) {
			if (DEBUG_HA)
				System.out.println("rule: " + rule);
			inputI = rule.getSrcStates().iterator();
			HedgeState<G_State> in1 = inputI.next();
			if (DEBUG_HA)
				System.out.println("input: " + in1);
			final GraphNode<G_Symbol, G_State> grNode = nodes.get(in1);
			if (DEBUG_HA)
				System.out.println("set starting");
			grNode.setNeeded();
			in1 = rule.getDestState();
			if (nodes.containsKey(in1)) {
				nodes.get(rule.getDestState()).setNeeded();
				if (DEBUG_HA)
					System.out.println("setting " + in1 + " end node");
			}
		}
		if (DEBUG_HA)
			System.out.println("checking needed nodes done");
		if (DEBUG_HA) {
			System.out.println("b4:");
			for (final HedgeState<G_State> st : nodes.keySet()) {
				System.out.println("--->" + st + ":\n--->" + nodes.get(st)
						+ ":\n" + nodes.get(st).getString());
			}
			if (DEBUG_HA)
				System.out.println("generation on incoming nodes - done");
		}
		// execute the elemination algorythm by trying to delete all nodes.
		// the needed nodes wont delete themselfes completely. just gather the
		// information
		// and send some to the neighbors
		for (final GraphNode<G_Symbol, G_State> node : nodes.values()) {
			node.delete();
		}
		if (DEBUG_HA) {
			System.out.println("after:");
			for (final HedgeState<G_State> st : nodes.keySet()) {
				System.out.println("--->" + st + ":\n--->" + nodes.get(st)
						+ ":\n" + nodes.get(st).getString());
			}
			System.out.println("---");
		}
		/*
		 * System.out.println("Expressions:"); for (GraphNode node :
		 * nodes.values()){ System.out.println(node +
		 * ": "+node.getExpression().toString()); }
		 * System.out.println("Expressions end");
		 */
		// the elemination algorythm minimized the graph and generated needed
		// expressions in the nodes
		// so we just call the expressions from the nodes
		if (DEBUG_HA)
			System.out.println("starting generation of expressions");
		for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : userRules) {
			if (DEBUG_HA)
				System.out.println("starting from rule " + rule);
			inputI = rule.getSrcStates().iterator();
			in = inputI.next();
			if (DEBUG_HA)
				System.out.println("checking input " + in);
			final RegularExpression<G_Symbol, G_State> inExp;
			// if the state is not in the cons rules it has to indicate the
			// recognition of the nil symbol
			// therefore it has to be in the collection with the nil rules
			if (nodes.containsKey(in)) {
				if (DEBUG_HA)
					System.out.println("its from cons rule");
				inExp = nodes.get(in).getExpression();
				assert inExp != null;
			} else {
				if (DEBUG_HA)
					System.out.println("its from nil rule");
				assert nilRules.contains(in);
				inExp = emptyExpression;
			}
			// create the hedge rule from the gathered information
			myRules.add(new HedgeRule<G_Symbol, G_State>(rule.getSymbol()
					.getOriginal(), inExp, rule.getDestState().getOriginal()));
			myStates.add(rule.getDestState().getOriginal());
		}
		if (DEBUG_HA)
			System.out.println("generation of expressions complete");
		final Set<G_State> myFinalStates = new HashSet<G_State>();
		// add all the accessible final states to the set of the final states
		// for the generated HA
		for (final G_State state : HedgeState.extractOriginal(TA
				.getFinalStates()))
			if (myStates.contains(state))
				myFinalStates.add(state);
		this.states = myStates;
		this.finalStates = myFinalStates;
		this.rules = myRules;
	}

	/**
	 * Removes rules, which do not correspond to the structure of transformed
	 * hedge automata these will never be used and cause problems on
	 * reconstruction.
	 *
	 * @param <G_State>  state type of transformed hedge automaton
	 * @param <G_Symbol> symbol type of transformed hedge automaton
	 * @param TA				 the tree automaton to be cleaned
	 * @return tree automaton without rules, which do not correnpond to the
	 *         structure of transformed hedge automatons
	 */
	private static <G_State extends State, G_Symbol extends UnrankedSymbol> FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> clean(
			final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TA) {
		final Collection<HedgeState<G_State>> consStates = new HashSet<HedgeState<G_State>>();
		final Collection<HedgeState<G_State>> nilStates = new HashSet<HedgeState<G_State>>();
		final Collection<HedgeState<G_State>> userStates = new HashSet<HedgeState<G_State>>();
		List<HedgeState<G_State>> input;
		for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : TA
				.getRules()) {
			input = rule.getSrcStates();
			switch (input.size()) {
				case 0:
					nilStates.add(rule.getDestState());
					break;
				case 1:
					userStates.add(rule.getDestState());
					break;
				case 2:
					consStates.add(rule.getDestState());
					break;
				default:
					throw new InputMismatchException(
							"Found a rule with arity more than 2. This rule breaks hedge automaton concept.");
			}
		}
		final Set<FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> rules = new HashSet<FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : TA
				.getRules()) {
			input = rule.getSrcStates();
			final HedgeState<G_State> st2;
			final HedgeState<G_State> st1;
			switch (input.size()) {
				case 0:
					rules.add(rule);
					break;
				case 1:
					st1 = input.get(0);
					if (consStates.contains(st1) || nilStates.contains(st1))
						rules.add(rule);
					break;
				case 2:
					st1 = input.get(0);
					st2 = input.get(1);
					if ((consStates.contains(st1) || nilStates.contains(st1))
							&& userStates.contains(st2))
						rules.add(rule);
					break;
				default:
					throw new InputMismatchException(
							"Found a rule with arity more than 2. This rule breaks hedge automaton concept.");
			}
		}
		final HashSet<HedgeState<G_State>> states = new HashSet<HedgeState<G_State>>();
		final HashSet<HedgeState<G_State>> finStates = new HashSet<HedgeState<G_State>>();
		for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : rules) {
			states.add(rule.getDestState());
			for (final HedgeState<G_State> state : rule.getSrcStates())
				states.add(state);
		}
		for (final HedgeState<G_State> state : TA.getFinalStates())
			if (states.contains(state))
				finStates.add(state);
		return new GenFTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(
				rules, finStates);
	}

	/**
	 * @return the set of final states of the hedge automaton
	 */
	public Collection<G_State> getFinalStates() {
		if (this.finalStates == null)
			return HedgeState.extractOriginal(TA.getFinalStates());
		else
			return this.finalStates;
	}

	/**
	 * @return the set of states of the hedge automaton
	 */
	public Collection<G_State> getStates() {
		if (this.states == null)
			return HedgeState.extractOriginal(TA.getStates());
		else
			return this.states;
	}

	/**
	 * @return the set of rules of the hedge automaton
	 */
	public Set<HedgeRule<G_Symbol, G_State>> getRules() {
		if (this.rules == null)
			TA2HA();
		return this.rules;
	}

	/**
	 * adds a set of states to the final states of the hedge automaton
	 *
	 * @param states
	 *            set of states to make final
	public void makeFinal(final Collection<G_State> states) {
	if (this.finalStates != null)
	this.finalStates.addAll(states);
	if (this.TA != null) {
	for (HedgeState<G_State> q : HedgeStateCache.getState(states))
	this.TA.addToFinals(q);
	}
	}
	 */

	/**
	 * adds a state to the final states of the hedge automaton
	 *
	 * @param state
	 *            state to be added to the final states
	public void makeFinal(final G_State state) {
	if (this.finalStates != null)
	this.finalStates.add(state);
	if (this.TA != null)
	this.TA.addToFinals(HedgeStateCache.getState(state));
	}
	 */

	/**
	 * Adds a rule to the rules of the hedge automaton.
	 *
	 * @param rule rule to be added
	 */
	public void addRule(final HedgeRule<G_Symbol, G_State> rule) {
		if (this.rules == null)
			TA2HA();
		this.rules.add(rule);
		this.TA = null;
	}

	/**
	 * Removes rule from the set of rules of the hedge automaton.
	 *
	 * @param rule to be removed
	 */
	public void removeRule(final HedgeRule<G_Symbol, G_State> rule) {
		if (this.rules == null)
			TA2HA();
		this.rules.remove(rule);
		this.TA = null;
	}

	/**
	 * Adds a state to the set of states of the hedge automaton.
	 *
	 * @param state
	 *            state to be added
	public void addState(final G_State state) {
	if (this.states != null)
	this.states.add(state);
	if (this.TA != null)
	this.TA.addState(HedgeStateCache.getState(state));
	}
	 */

	/**
	 * Returns all states, which are not final.
	 *
	 * @return states, which are not final
	 */
	public Collection<G_State> getNonFinalStates() {
		final Collection<G_State> result = new HashSet<G_State>();
		if (this.states != null) {
			for (final G_State state : this.states)
				if (!this.finalStates.contains(state))
					result.add(state);
			return result;
		}
		for (final HedgeState<G_State> state : this.TA.getStates())
			if (!this.TA.getFinalStates().contains(state))
				result.add(state.getOriginal());
		return result;
	}

	/**
	 * Returns the alphabet of symbols, which are contained in the rules of the
	 * hedge automaton.
	 *
	 * @return the set of symbols
	 */
	public Collection<G_Symbol> createAlphabet() {
		final Collection<G_Symbol> result = new HashSet<G_Symbol>();
		if (this.rules != null)
			for (final HedgeRule<G_Symbol, G_State> rule : this.rules)
				result.add(rule.getSymbol());
		else
			for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : this.TA
					.getRules()) {
				final HedgeSymbol<G_Symbol> sym = rule.getSymbol();
				if (sym.isPacked())
					result.add(sym.getOriginal());
			}
		return result;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if (this.states == null)
			TA2HA();
		return "Zustände:\n" + this.states + "\n=========\nEndzustände:\n"
				+ this.finalStates + "\n=========\nRegeln:\n" + this.rules
				+ "\n=========\n";
	}

	/**
	 * Checks whether the automaton contains given state.
	 *
	 * @param state State to check out
	 * @return whether the automaton contains given state
	 */
	public boolean containsState(final G_State state) {
		if (this.states != null)
			return this.states.contains(state);
		return HedgeState.extractOriginal(this.TA.getStates()).contains(state);
	}

	/**
	 * Checks whether the automaton contains given state.
	 *
	 * @param state State to check out
	 * @return whether the automaton contains given state
	 */
	public boolean containsFinalState(final G_State state) {
		if (this.finalStates != null)
			return this.finalStates.contains(state);
		return HedgeState.extractOriginal(this.TA.getFinalStates()).contains(
				state);
	}

	/**
	 * Checks whether the automaton contains given rule.
	 *
	 * @param rule Rule to check out
	 * @return whether the automaton contains given rule
	 */
	public boolean containsRule(final HedgeRule<G_Symbol, G_State> rule) {
		if (this.rules == null)
			TA2HA();
		return this.rules.contains(rule);
	}

	/**
	 * Toggles the generation of the FTA from this HA if needed. Returns the
	 * generated FTA.
	 *
	 * @return the FTA representation of this HA
	 */
	public FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> getTA() {
		if (this.TA == null)
			HA2TA();
		return this.TA;
	}
}
