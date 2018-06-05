/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE SyntaxChecker plug-in.
 *
 * The ULTIMATE SyntaxChecker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SyntaxChecker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SyntaxChecker plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SyntaxChecker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SyntaxChecker plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.syntaxchecker;

import de.uni_freiburg.informatik.ultimate.cdt.decorator.ASTDecorator;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Extract filename of input from C AST.
 *
 * @author Matthias Heizmann
 */
public class FilenameExtractionObserver extends BaseObserver {

	private String mFilename;
	private final ILogger mLogger;

	public FilenameExtractionObserver(final ILogger logger) {
		mLogger = logger;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (!(root instanceof WrapperNode)) {
			mLogger.warn("Seen unsupported model: " + root.getClass().getCanonicalName());
			return false;
		}
		final WrapperNode wn = (WrapperNode) root;
		final ASTDecorator tu = (ASTDecorator) wn.getBacking();
		if (tu.getUnits().size() != 1) {
			throw new UnsupportedOperationException("SyntaxChecker does not support multiple files");
		}
		final String filename = tu.getUnit(0).getSourceTranslationUnit().getFileLocation().getFileName();
		if (mFilename == null) {
			mFilename = filename;
		} else {
			throw new IllegalStateException("mFilename already set");
		}
		return false;
	}

	public String getFilename() {
		return mFilename;
	}

}
