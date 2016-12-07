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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IBinding;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.RewriteUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Removes unreferenced functions, structs, unions and enums. Includes prototypes and forward declarations. The note
 * about performance of {@link RemoveUnreferencedDecls} applies here as well.
 */
public final class RemoveUnreferencedObjects implements IVariantGenerator {
	private final ISourceDocument mSource;
	private final List<ObjChange> mChanges;

	private RemoveUnreferencedObjects(final ISourceDocument source, final List<ObjChange> changes) {
		mSource = source;
		mChanges = changes;
	}

	@Override
	public String apply(final List<IChangeHandle> activeChanges) {
		final SourceRewriter rewriter = new SourceRewriter(mSource);
		activeChanges.stream().forEach(c -> ((ObjChange) c).apply(rewriter));
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
		return analyze(context, EnumSet.allOf(ObjFlag.class));
	}

	/**
	 * @param context
	 *            Pass context.
	 * @param options
	 *            set of options.
	 * @return result optional generator instance
	 */
	public static Optional<IVariantGenerator> analyze(final IPassContext context, final Set<ObjFlag> options) {
		final List<ObjChange> changes = collectChanges(context.getSharedPst(), options);
		return changes.isEmpty() ? Optional.empty()
				: Optional.of(new RemoveUnreferencedObjects(context.getInput(), changes));
	}

	private static List<ObjChange> collectChanges(final IPSTTranslationUnit tu, final Set<ObjFlag> options) {
		final Map<IBinding, List<IPSTNode>> funcs = new HashMap<>();
		tu.accept(new BindingCollector(options, funcs));
		final List<ObjChange> changes = new ArrayList<>(funcs.size());
		for (Entry<IBinding, List<IPSTNode>> entry : funcs.entrySet()) {
			changes.add(new ObjChange(changes.size(), entry.getKey().getNameCharArray().toString(), entry.getValue()));
		}
		return changes;
	}

	private static class ObjChange implements IChangeHandle {
		private final int mIndex;
		private final String mName;
		private final List<IPSTNode> mNodes;

		public ObjChange(final int index, final String name, final List<IPSTNode> nodes) {
			mIndex = index;
			mName = name;
			mNodes = nodes;
		}

		void apply(final SourceRewriter rewriter) {
			for (IPSTNode node : mNodes) {
				rewriter.replace(node, RewriteUtils.getReplacementStringForSafeDeletion(node));
			}
		}

		@Override
		public int getSequenceIndex() {
			return mIndex;
		}

		@Override
		public String toString() {
			return "Remove unreferenced object " + mName + " ["
					+ mNodes.stream().map(Object::toString).collect(Collectors.joining(", ")) + "]";
		}
	}
}
