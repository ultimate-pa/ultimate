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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.DefaultParser;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.IParser;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.StringSourceDocument;

/**
 * A default {@link IPassContext}.
 */
public class DefaultPassContext implements IPassContext {
	private final ISourceDocument mInput;
	private final IParser mParser;
	private volatile IASTTranslationUnit mAst;
	private volatile IPSTTranslationUnit mPst;
	private final ILogger mLogger;
	
	/**
	 * @param input
	 *            Input.
	 * @param logger
	 *            logger
	 */
	public DefaultPassContext(final ISourceDocument input, final ILogger logger) {
		this(input, new DefaultParser(logger), logger);
	}
	
	/**
	 * @param input
	 *            Input.
	 * @param parser
	 *            parser
	 * @param logger
	 *            logger
	 */
	public DefaultPassContext(final ISourceDocument input, final IParser parser, final ILogger logger) {
		mInput = input;
		mParser = parser;
		mLogger = logger;
	}
	
	/**
	 * @param input
	 *            Input string.
	 * @param logger
	 *            logger
	 */
	public DefaultPassContext(final String input, final ILogger logger) {
		this(new StringSourceDocument(input), logger);
	}
	
	/**
	 * @param input
	 *            Input string.
	 * @param parser
	 *            parser
	 * @param logger
	 *            logger
	 */
	public DefaultPassContext(final String input, final IParser parser, final ILogger logger) {
		this(new StringSourceDocument(input), parser, logger);
	}
	
	@Override
	public ISourceDocument getInput() {
		return mInput;
	}
	
	@Override
	public IParser getParser() {
		return mParser;
	}
	
	@Override
	public IASTTranslationUnit getSharedAst() {
		if (mAst == null) {
			synchronized (this) {
				if (mAst == null) {
					mAst = mParser.parse(mInput.getText());
				}
			}
		}
		return mAst;
	}
	
	@Override
	public IPSTTranslationUnit getSharedPst() {
		if (mPst == null) {
			synchronized (this) {
				if (mPst == null) {
					mPst = mParser.createPst(getSharedAst(), mInput);
				}
			}
		}
		return mPst;
	}

	@Override
	public ILogger getLogger() {
		return mLogger;
	}
}
