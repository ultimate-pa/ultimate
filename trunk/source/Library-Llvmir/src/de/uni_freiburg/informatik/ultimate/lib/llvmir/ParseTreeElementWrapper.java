/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE Library-Llvmir plug-in.
 * It is used to wrap a ParseTree as an IElement.
 *
 * The ULTIMATE Library-Llvmir plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Llvmir plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Llvmir plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Llvmir plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Llvmir plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.llvmir;

import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;

public class ParseTreeElementWrapper implements IElement {
	private static final long serialVersionUID = 233243407316309392L;
	private final IPayload mPayload;
	private final ParseTree mParseTree;
	private final String mFilename;

	/**
	 * Constructs a wrapper for a ParseTree that implements the IElement interface.
	 *
	 * @param parseTree The ParseTree to wrap.
	 * @param filename  The name of the file from which the ParseTree was generated.
	 */
	public ParseTreeElementWrapper(final ParseTree parseTree, final String filename) {
		mParseTree = parseTree;
		mFilename = filename;
		mPayload = new Payload();
	}

	@Override
	public IPayload getPayload() {
		if (!hasPayload()) {
			return new Payload();
		}
		return mPayload;
	}

	@Override
	public boolean hasPayload() {
		if (mPayload == null) {
			return false;
		}
		return true;
	}

	/**
	 * Returns the ParseTree wrapped by this element.
	 *
	 * @return The ParseTree wrapped by this element.
	 */
	public ParseTree getParseTree() {
		return mParseTree;
	}

	/**
	 * Returns the filename from which the ParseTree was generated.
	 *
	 * @return The filename from which the ParseTree was generated.
	 */
	public String getFilename() {
		return mFilename;
	}

}
