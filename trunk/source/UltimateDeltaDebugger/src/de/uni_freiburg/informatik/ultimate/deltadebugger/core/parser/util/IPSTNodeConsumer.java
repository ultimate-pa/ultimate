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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTACSLNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTPreprocessorNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;

/**
 * Simulate a double dispatch function for an IPSTNode argument. Analogous to IASTNodeConsumer for consistency reasons.
 *
 */
@FunctionalInterface
public interface IPSTNodeConsumer {

	default void on(final IPSTComment comment) {
		on((IPSTPreprocessorNode) comment);
	}

	default void on(final IPSTACSLComment acslComment) {
		on((IPSTComment) acslComment);
	}
	
	default void on(final IPSTACSLNode acslNode) {
		on((IPSTNode) acslNode);
	}
	
	default void on(final IPSTConditionalBlock conditionalBlock) {
		on((IPSTNode) conditionalBlock);
	}

	default void on(final IPSTDirective directive) {
		on((IPSTPreprocessorNode) directive);
	}

	default void on(final IPSTIncludeDirective includeDirective) {
		on((IPSTDirective) includeDirective);
	}

	default void on(final IPSTLiteralRegion literalRegion) {
		on((IPSTNode) literalRegion);
	}

	default void on(final IPSTMacroExpansion macroExpansion) {
		on((IPSTPreprocessorNode) macroExpansion);
	}

	void on(IPSTNode node);

	default void on(final IPSTPreprocessorNode preprocessOrNode) {
		on((IPSTNode) preprocessOrNode);
	}

	default void on(final IPSTRegularNode node) {
		on((IPSTNode) node);
	}

	default void on(final IPSTTranslationUnit translationUnit) {
		on((IPSTRegularNode) translationUnit);
	}
}
