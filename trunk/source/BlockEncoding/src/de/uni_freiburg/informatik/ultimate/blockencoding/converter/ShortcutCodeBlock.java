package de.uni_freiburg.informatik.ultimate.blockencoding.converter;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

/**
 * This is basically a dummy code block, which we need while converting a
 * shortcut edge (to an error location). For the RCFG we have to use a so called
 * InterproceduralSeqComposition, because this can handle more Calls then
 * Returns. During the Conversion we store all involved CodeBlocks here, for
 * later use it in the InterproceduralSequentialCompositon.
 * 
 * @author Stefan Wissert
 * 
 */
public class ShortcutCodeBlock extends CodeBlock {

	private CodeBlock[] codeBlocks;

	/**
	 * @param source
	 * @param target
	 * @param codeBlocks
	 */
	public ShortcutCodeBlock(ProgramPoint source, ProgramPoint target,
			CodeBlock[] codeBlocks) {
		super(source, target);
		this.codeBlocks = codeBlocks;
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg
	 * .CodeBlock#getFieldNames()
	 */
	@Override
	protected String[] getFieldNames() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg
	 * .CodeBlock#getPrettyPrintedStatements()
	 */
	@Override
	public String getPrettyPrintedStatements() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg
	 * .CodeBlock
	 * #getCopy(de.uni_freiburg.informatik.ultimate.plugins.generator.
	 * rcfgbuilder .cfg.ProgramPoint,
	 * de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder
	 * .cfg.ProgramPoint)
	 */
	@Override
	public CodeBlock getCopy(ProgramPoint source, ProgramPoint target) {
		return null;
	}

	/**
	 * @return the codeBlocks
	 */
	public CodeBlock[] getCodeBlocks() {
		return codeBlocks;
	}

}
