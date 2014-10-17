package de.uni_freiburg.informatik.ultimatetest.evals;

import de.uni_freiburg.informatik.ultimatetest.evals.TACAS2015Summary.Aggregate;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ColumnDefinition {
	private final String ColumnToKeep;
	private final String LatexTableTitle;
	private final ConversionContext ConversionContext;
	private final Aggregate SingleRunToOneRow;
	private final Aggregate ManyRunsToOneRow;

	public ColumnDefinition(String csvColumnName, String latexTableTitle, ConversionContext humanReadable,
			Aggregate howToAggregateFromSingleRun, Aggregate howToAggregateForLatexTableRow) {
		ColumnToKeep = csvColumnName;
		LatexTableTitle = latexTableTitle;
		ConversionContext = humanReadable;
		SingleRunToOneRow = howToAggregateFromSingleRun;
		ManyRunsToOneRow = howToAggregateForLatexTableRow;
	}

	public String getColumnToKeep() {
		return ColumnToKeep;
	}

	public String getLatexTableTitle() {
		return LatexTableTitle;
	}

	public ConversionContext getConversionContext() {
		return ConversionContext;
	}

	public Aggregate getSingleRunToOneRow() {
		return SingleRunToOneRow;
	}

	public Aggregate getManyRunsToOneRow() {
		return ManyRunsToOneRow;
	}
}