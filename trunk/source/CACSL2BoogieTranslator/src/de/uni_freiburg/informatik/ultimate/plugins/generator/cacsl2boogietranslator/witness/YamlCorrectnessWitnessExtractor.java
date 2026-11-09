/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IVariable;

import de.uni_freiburg.informatik.ultimate.cdt.translation.LineOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.FunctionContract;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.GhostVariable;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationTransitionInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopTransitionInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

/**
 * Extract a correctness witness from a YAML-based witness file.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class YamlCorrectnessWitnessExtractor extends CorrectnessWitnessExtractor {
	private Witness mWitness;
	private int mPrevVariableCounter = 0;

	public YamlCorrectnessWitnessExtractor(final IUltimateServiceProvider service) {
		super(service);
	}

	public void setWitness(final Witness witness) {
		mWitness = witness;
	}

	@Override
	public boolean isReady() {
		return mWitness != null && mTranslationUnit != null;
	}

	@Override
	protected IExtractedCorrectnessWitness extractWitness() {
		// TODO: The column extraction happens in LocationFactory, so we create one as a workaround
		final LocationFactory locationFactory =
				new LocationFactory(null, new LineOffsetComputer(mTranslationUnit.getRawSignature()));
		final Map<IASTNode, ExtractedLoopInvariant> loopInvariants = new HashMap<>();
		final Map<IASTNode, ExtractedLocationInvariant> locationInvariants = new HashMap<>();
		final YamlExtractedCorrectnessWitness rtr = new YamlExtractedCorrectnessWitness();
		for (final WitnessEntry entry : mWitness.getEntries()) {
			final Location location;
			final Consumer<IASTNode> addFunction;
			if (entry instanceof GhostVariable) {
				final GhostVariable ghost = (GhostVariable) entry;
				rtr.addGlobalDeclaration(new ExtractedGhostVariable(ghost.getVariable(), ghost.getInitialValue(),
						ghost.getType(), mTranslationUnit));
				mStats.success();
				continue;
			}
			if (entry instanceof LocationInvariant) {
				location = ((LocationInvariant) entry).getLocation();
				addFunction = node -> addLocationInvariant((LocationInvariant) entry, node, locationInvariants);
			} else if (entry instanceof LoopInvariant) {
				location = ((LoopInvariant) entry).getLocation();
				addFunction = node -> addLoopInvariant((LoopInvariant) entry, node, loopInvariants);
			} else if (entry instanceof FunctionContract) {
				location = ((FunctionContract) entry).getLocation();
				addFunction = node -> addFunctionContract((FunctionContract) entry, node, rtr);
			} else if (entry instanceof GhostUpdate) {
				final GhostUpdate update = (GhostUpdate) entry;
				location = update.getLocation();
				addFunction = node -> rtr.addGhostUpdate(node,
						new ExtractedGhostUpdate(update.getVariable(), update.getValue(), node, true));
			} else if (entry instanceof LoopTransitionInvariant) {
				location = ((LoopTransitionInvariant) entry).getLocation();
				addFunction = node -> addLoopTransitionInvariant(((LoopTransitionInvariant) entry), node, rtr);
			} else if (entry instanceof LocationTransitionInvariant) {
				location = ((LocationTransitionInvariant) entry).getLocation();
				addFunction = node -> addLocationTransitionInvariant((LocationTransitionInvariant) entry, node, rtr);
			} else {
				throw new UnsupportedOperationException("Unknown entry type " + entry.getClass().getSimpleName());
			}
			final LineColumnMatchingVisitor visitor = new LineColumnMatchingVisitor(location, locationFactory);
			visitor.run(mTranslationUnit);
			final IASTNode node = visitor.getMatchedNode();
			if (node == null) {
				if (mIgnoreUnmatchedEntries) {
					mStats.fail();
					continue;
				}
				throw new UnsupportedOperationException("The following witness entry could not be matched: " + entry);
			}
			addFunction.accept(node);
			mStats.success();
		}
		loopInvariants.forEach(rtr::addInvariant);
		locationInvariants.forEach(rtr::addInvariant);
		return rtr;

	}

	private void addLoopTransitionInvariant(final LoopTransitionInvariant loopTransitionInvariant, final IASTNode node,
			final YamlExtractedCorrectnessWitness result) {
		if (!(node instanceof IASTWhileStatement) && !(node instanceof IASTForStatement)
				&& !(node instanceof IASTDoStatement)) {
			throw new UnsupportedOperationException("Loop transition invariant is only allowed at loop (found "
					+ node.getClass().getSimpleName() + ")");
		}
		result.addInvariant(node, new ExtractedLoopInvariant(
				instrumentTransitionInvariant(loopTransitionInvariant.getInvariant(), node, result), node));
	}

	private void addLocationTransitionInvariant(final LocationTransitionInvariant locationTransitionInvariant,
			final IASTNode node, final YamlExtractedCorrectnessWitness result) {
		result.addInvariant(node, new ExtractedLocationInvariant(
				instrumentTransitionInvariant(locationTransitionInvariant.getInvariant(), node, result), node, true));
	}

	/**
	 * Rewrites the given {@code transitionInvariant} as a usual invariant by introducing ghost variables
	 * {@code last_prev_x} and {@code any_prev_x} to reflect the effects of {@code \\at(x, LastPrev)} and
	 * {@code \\at(x, AnyPrev)}.
	 */
	private String instrumentTransitionInvariant(final String transitionInvariant, final IASTNode node,
			final YamlExtractedCorrectnessWitness result) {
		// Search for \at(x, LastPrev) and \at(x, AnyPrev) in the transition invariant and replaces their occurrences
		// with fresh ghost variables that are then collected in a map.
		final Map<PrevVar, String> replacements = new HashMap<>();
		final Pattern pattern =
				Pattern.compile("\\\\at\\s*\\(\\s*([A-Za-z_][A-Za-z0-9_]*)\\s*,\\s*(LastPrev|AnyPrev)\\s*\\)");
		final Matcher matcher = pattern.matcher(transitionInvariant);
		final StringBuilder replacedInvariant = new StringBuilder();
		while (matcher.find()) {
			final String variable = matcher.group(1);
			final boolean anyPrev = "AnyPrev".equals(matcher.group(2));
			final PrevVar key = new PrevVar(variable, anyPrev);
			final String repl = replacements.computeIfAbsent(key,
					x -> freshVariableName((anyPrev ? "any_prev_" : "last_prev_") + variable));
			matcher.appendReplacement(replacedInvariant, Matcher.quoteReplacement(repl));
		}
		matcher.appendTail(replacedInvariant);
		if (replacements.isEmpty()) {
			// There is no \at, nothing to do
			return transitionInvariant;
		}
		String nondet = null;
		// Introduce a ghost variable to track, whether the invariant is supposed to hold. It should hold trivially in
		// the first loop iteration.
		final String shouldHold = freshVariableName("transition_invariant_should_hold");
		result.addGlobalDeclaration(new ExtractedGhostVariable(shouldHold, "0", "int", mTranslationUnit));
		for (final Entry<PrevVar, String> repl : replacements.entrySet()) {
			final String variable = repl.getKey().variable();
			final String type = findVariableType(node, variable);
			final String replGhost = repl.getValue();
			if (type == null) {
				throw new UnsupportedOperationException("Unable to determine the type of variable " + variable);
			}
			// Introduce a ghost variable to track the previous values of x (any_prev_x or last_prev_x)
			result.addGlobalDeclaration(new ExtractedGhostVariable(replGhost, "0", type, mTranslationUnit));
			if (repl.getKey().isAnyPrev()) {
				if (nondet == null) {
					// For AnyPrev, introduce another ghost variable for a non-deterministic choice. This
					// non-determinism allows us to "access" all values of previous iterations.
					// Note: It is important that all \at-expressions share their non-deterministic choice, as the
					// result of \at should always refer to the same iteration.
					nondet = freshVariableName("any_prev_nondet");
					result.addGlobalDeclaration(new ExtractedGhostVariable(nondet, "0", "int", mTranslationUnit));
					result.addGhostUpdate(node,
							new ExtractedGhostUpdate(nondet, "__VERIFIER_nondet_int()", node, false));
				}
				// Based on the value of this non-deterministic ghost variable, either set any_prev_x to x or keep its
				// previous value.
				result.addGhostUpdate(node, new ExtractedGhostUpdate(replGhost,
						nondet + " ? " + variable + " : " + replGhost, node, false));
				// transition_invariant_should_hold := transition_invariant_should_hold || any_prev_nondet;
				result.addGhostUpdate(node,
						new ExtractedGhostUpdate(shouldHold, shouldHold + " || " + nondet, node, false));
			} else {
				// For LastPrev, just assign last_prev_x to x and transition_invariant_should_hold to 1.
				result.addGhostUpdate(node, new ExtractedGhostUpdate(replGhost, variable, node, false));
				result.addGhostUpdate(node, new ExtractedGhostUpdate(shouldHold, "1", node, false));
			}
		}
		return "!" + shouldHold + " || (" + replacedInvariant + ")";
	}

	private String freshVariableName(final String variable) {
		return variable + "_" + mPrevVariableCounter++;
	}

	private record PrevVar(String variable, boolean isAnyPrev) {
	}

	private String findVariableType(final IASTNode scope, final String variable) {
		final class VariableTypeVisitor extends ASTGenericVisitor {
			private String mType;

			private VariableTypeVisitor() {
				super(true);
			}

			@Override
			protected int genericVisit(final IASTNode current) {
				if (current instanceof final IASTName name && variable.equals(name.toString())) {
					final IBinding binding = name.resolveBinding();
					if (binding instanceof final IVariable variableBinding) {
						mType = variableBinding.getType().toString();
						return PROCESS_ABORT;
					}
				}
				return PROCESS_CONTINUE;
			}
		}
		final VariableTypeVisitor visitor = new VariableTypeVisitor();
		scope.accept(visitor);
		if (visitor.mType == null) {
			mTranslationUnit.accept(visitor);
		}
		return visitor.mType;
	}

	private static void addFunctionContract(final FunctionContract functionContract, final IASTNode node,
			final YamlExtractedCorrectnessWitness result) {
		if (!(node instanceof IASTSimpleDeclaration) && !(node instanceof IASTFunctionDefinition)) {
			throw new UnsupportedOperationException(
					"Function contract is only allowed at declaration or definition of a function (found "
							+ node.getClass().getSimpleName() + ")");
		}
		result.addFunctionContract(node,
				new ExtractedFunctionContract(functionContract.getRequires(), functionContract.getEnsures(), node));
	}

	private static void addLocationInvariant(final LocationInvariant current, final IASTNode node,
			final Map<IASTNode, ExtractedLocationInvariant> locationInvariants) {
		String invariant = current.getInvariant();
		final ExtractedLocationInvariant old = locationInvariants.get(node);
		if (old != null) {
			invariant = conjunctInvariants(old.getInvariant(), invariant);
		}
		locationInvariants.put(node, new ExtractedLocationInvariant(invariant, node, true));
	}

	private static void addLoopInvariant(final LoopInvariant current, final IASTNode node,
			final Map<IASTNode, ExtractedLoopInvariant> loopInvariants) {
		if (!(node instanceof IASTWhileStatement) && !(node instanceof IASTForStatement)
				&& !(node instanceof IASTDoStatement)) {
			throw new UnsupportedOperationException(
					"Loop invariant is only allowed at loop (found " + node.getClass().getSimpleName() + ")");
		}
		String invariant = current.getInvariant();
		final ExtractedLoopInvariant old = loopInvariants.get(node);
		if (old != null) {
			invariant = conjunctInvariants(old.getInvariant(), invariant);
		}
		loopInvariants.put(node, new ExtractedLoopInvariant(invariant, node));
	}

	private static String conjunctInvariants(final String invariant1, final String invariant2) {
		return "(" + invariant1 + ") && (" + invariant2 + ")";
	}

	private static final class LineColumnMatchingVisitor extends ASTGenericVisitor {
		private IASTNode mMatchedNode;
		private final Location mLocation;
		private final LocationFactory mLocationFactory;

		public LineColumnMatchingVisitor(final Location location, final LocationFactory locationFactory) {
			super(true);
			mLocation = location;
			mLocationFactory = locationFactory;
		}

		public void run(final IASTTranslationUnit translationUnit) {
			translationUnit.accept(this);
		}

		public IASTNode getMatchedNode() {
			return mMatchedNode;
		}

		@Override
		protected int genericVisit(final IASTNode node) {
			if (node instanceof IASTTranslationUnit) {
				return PROCESS_CONTINUE;
			}
			final ILocation loc = mLocationFactory.createCLocation(node);
			if (loc == null) {
				return PROCESS_CONTINUE;
			}
			// Match before the AST node, if the line matches and either the column is not present (it can be omitted;
			// should be matched the first node of the line in that case) or it also matches the AST node
			if (mLocation.getLine() == loc.getStartLine()
					&& (mLocation.getColumn() == null || mLocation.getColumn() == loc.getStartColumn())) {
				mMatchedNode = node;
				// Abort the search, since we want the witness entry to be matched at most once.
				return PROCESS_ABORT;
			}
			return PROCESS_CONTINUE;
		}
	}

	private static final class YamlExtractedCorrectnessWitness implements IExtractedCorrectnessWitness {
		private final HashRelation<IASTNode, ExtractedWitnessInvariant> mInvariants = new HashRelation<>();
		private final HashRelation<IASTNode, ExtractedFunctionContract> mFunctionContracts = new HashRelation<>();
		private final Map<IASTNode, List<ExtractedGhostUpdate>> mGhostUpdates = new HashMap<>();
		private final Set<IExtractedWitnessDeclaration> mGlobalDeclarations = new HashSet<>();

		private void addInvariant(final IASTNode node, final ExtractedWitnessInvariant entry) {
			mInvariants.addPair(node, entry);
		}

		private void addFunctionContract(final IASTNode function, final ExtractedFunctionContract contract) {
			mFunctionContracts.addPair(function, contract);
		}

		private void addGhostUpdate(final IASTNode node, final ExtractedGhostUpdate update) {
			mGhostUpdates.computeIfAbsent(node, x -> new ArrayList<>()).add(update);
		}

		private void addGlobalDeclaration(final IExtractedWitnessDeclaration declaration) {
			mGlobalDeclarations.add(declaration);
		}

		@Override
		public Set<ExtractedWitnessInvariant> getInvariants(final IASTNode node) {
			return mInvariants.getImage(node);
		}

		@Override
		public Set<ExtractedFunctionContract> getFunctionContracts(final IASTNode node) {
			return mFunctionContracts.getImage(node);
		}

		@Override
		public List<ExtractedGhostUpdate> getGhostUpdates(final IASTNode node) {
			return mGhostUpdates.getOrDefault(node, List.of());
		}

		@Override
		public Set<IExtractedWitnessDeclaration> getGlobalDeclarations() {
			return Collections.unmodifiableSet(mGlobalDeclarations);
		}

		@Override
		public List<String> printAllEntries() {
			final List<String> result = new ArrayList<>();
			for (final Entry<IASTNode, ExtractedWitnessInvariant> entry : mInvariants.getSetOfPairs()) {
				result.add(entry.getValue().toString());
			}
			for (final Entry<IASTNode, ExtractedFunctionContract> entry : mFunctionContracts.getSetOfPairs()) {
				result.add(entry.getValue().toString());
			}
			for (final var d : mGlobalDeclarations) {
				result.add(d.toString());
			}
			for (final var updates : mGhostUpdates.values()) {
				for (final var u : updates) {
					result.add(u.toString());
				}
			}
			return result;
		}
	}
}
