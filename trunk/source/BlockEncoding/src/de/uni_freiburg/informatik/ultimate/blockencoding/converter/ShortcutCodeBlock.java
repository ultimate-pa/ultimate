/*
 * Copyright (C) 2013-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 *
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.converter;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * This is basically a dummy code block, which we need while converting a shortcut edge (to an error location). For the
 * RCFG we have to use a so called InterproceduralSeqComposition, because this can handle more Calls then Returns.
 * During the Conversion we store all involved CodeBlocks here, for later use it in the
 * InterproceduralSequentialCompositon.
 *
 * @author Stefan Wissert
 *
 */
public class ShortcutCodeBlock extends CodeBlock {

	private final CodeBlock[] mCodeBlocks;

	/**
	 * @param source
	 * @param target
	 * @param codeBlocks
	 * @param logger
	 */
	public ShortcutCodeBlock(final BoogieIcfgLocation source, final BoogieIcfgLocation target,
			final CodeBlock[] codeBlocks, final ILogger logger) {
		super(source, target, logger);
		mCodeBlocks = codeBlocks;
	}

	private static final long serialVersionUID = 1L;

	@Override
	public String getPrettyPrintedStatements() {
		return toString();
	}

	/**
	 * @return the codeBlocks
	 */
	public CodeBlock[] getCodeBlocks() {
		return mCodeBlocks;
	}

	@Override
	public String toString() {
		return "SHORTCUTCODEBLOCK";
	}

}
