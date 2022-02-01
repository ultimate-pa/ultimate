/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.ChangeConflictException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.CommaDeleter;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Removes unreferenced typedefs, variables and members in global or local scope. Supports deletion of individual comma
 * separated declarators from a single declaration. Individual enumerators could be supported as well, but that's not
 * implemented yet.
 * 
 * Performance is certainly far from optimal, because each element is checked individually for being unreferenced by
 * traversing the whole AST. It should be possible to improve performance by collecting unreferenced nodes in one
 * traversal.
 * 
 */
public final class RemoveUnreferencedDecls implements IVariantGenerator {
	private final ISourceDocument mSource;
	private final List<DeclPartChange> mChanges;

	private RemoveUnreferencedDecls(final ISourceDocument source, final List<DeclPartChange> changes) {
		mSource = source;
		mChanges = changes;
	}

	@Override
	public String apply(final List<IChangeHandle> activeChanges) {
		final Map<DeclParts, List<Integer>> activeParts = new IdentityHashMap<>();
		activeChanges.stream().forEachOrdered(c -> ((DeclPartChange) c).combine(activeParts));

		final SourceRewriter rewriter = new SourceRewriter(mSource);
		for (Entry<DeclParts, List<Integer>> entry : activeParts.entrySet()) {
			final DeclParts declParts = entry.getKey();
			final List<IPSTNode> nodesToDelete = entry.getValue().stream().sorted()
					.map(declParts.getUnreferencedDeclarators()::get).collect(Collectors.toList());

			// Delete the full declaration if all declarators are to be deleted
			if (nodesToDelete.size() == declParts.getAllDeclarators().size()) {
				// Delete leading macros
				declParts.getLeadingMacroExpansions().stream()
						.forEach(m -> rewriter.replace(m, RewriteUtils.getDeletionStringWithWhitespaces(m)));

				// Delete the whole thing if there is no referenced type specifier included
				if (!declParts.hasReferencedTypeSpecifier()) {
					rewriter.replace(declParts.getDeclaration(),
							RewriteUtils.getReplacementStringForSafeDeletion(declParts.getDeclaration()));
					continue;
				}

				// Delete only decl specifier tokens and individual declarators
				if (declParts.getTypeSpecifierTokens() == null) {
					throw new ChangeConflictException(
							"Cannot delete all declarators because of missing decl specifier tokens for "
									+ declParts.getDeclaration());
				}

				declParts.getTypeSpecifierTokens().stream().forEachOrdered(t -> rewriter.replace(t, " "));
			}
			CommaDeleter.deleteNodesWithComma(rewriter,
					nodesToDelete.stream().map(n -> (ISourceRange) n).collect(Collectors.toList()),
					declParts.getAllDeclarators());
		}
		return rewriter.apply();
	}

	@Override
	public List<IChangeHandle> getChanges() {
		return Collections.unmodifiableList(mChanges);
	}

	/**
	 * @param context
	 *            Pass context.
	 * @return result optional generator instance
	 */
	public static Optional<IVariantGenerator> analyze(final IPassContext context) {
		return analyze(context, EnumSet.allOf(DeclFlag.class));
	}

	/**
	 * @param context
	 *            Pass context.
	 * @param options
	 *            set of options.
	 * @return result optional generator instance
	 */
	public static Optional<IVariantGenerator> analyze(final IPassContext context, final Set<DeclFlag> options) {
		final List<DeclPartChange> changes = collectChanges(context.getSharedPst(), options);
		return changes.isEmpty() ? Optional.empty()
				: Optional.of(new RemoveUnreferencedDecls(context.getInput(), changes));
	}

	private static List<DeclPartChange> collectChanges(final IPSTTranslationUnit translationUnit,
			final Set<DeclFlag> options) {
		final List<DeclParts> listOfDeclParts = new ArrayList<>();
		translationUnit.accept(new DeclCollector(options, listOfDeclParts));
		final List<DeclPartChange> changes = new ArrayList<>();
		for (DeclParts declParts : listOfDeclParts) {
			for (int i = 0; i != declParts.getUnreferencedDeclarators().size(); ++i) {
				changes.add(new DeclPartChange(changes.size(), declParts, i));
			}
		}
		return changes;
	}

	/**
	 * A change handle.
	 */
	private static class DeclPartChange implements IChangeHandle {
		private final int mIndex;
		private final DeclParts mDeclParts;
		private final int mDeclaratorIndex;

		public DeclPartChange(final int index, final DeclParts declParts, final int declaratorIndex) {
			mIndex = index;
			mDeclParts = declParts;
			mDeclaratorIndex = declaratorIndex;
		}

		void combine(Map<DeclParts, List<Integer>> activeParts) {
			activeParts.computeIfAbsent(mDeclParts, t -> new ArrayList<>()).add(mDeclaratorIndex);
		}

		@Override
		public int getSequenceIndex() {
			return mIndex;
		}

		@Override
		public String toString() {
			return "Remove unreferenced declarator \""
					+ mDeclParts.getUnreferencedDeclaratorNames().get(mDeclaratorIndex) + "\" "
					+ mDeclParts.getUnreferencedDeclarators().get(mDeclaratorIndex);
		}
	}
}
