/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.summaries;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ColumnDefinition {
	public enum Aggregate {
		Sum, Max, Average, Ignore
	}

	private final String mColumnToKeep;
	private final String mLatexTableTitle;
	private final ConversionContext mConversionContext;
	private final Aggregate mSingleRunToOneRow;
	private final Aggregate mManyRunsToOneRow;

	public ColumnDefinition(String csvColumnName, String latexTableTitle, ConversionContext humanReadable,
			Aggregate howToAggregateFromSingleRun, Aggregate howToAggregateForLatexTableRow) {
		mColumnToKeep = csvColumnName;
		mLatexTableTitle = latexTableTitle;
		mConversionContext = humanReadable;
		mSingleRunToOneRow = howToAggregateFromSingleRun;
		mManyRunsToOneRow = howToAggregateForLatexTableRow;
	}

	public String getCsvColumnTitle() {
		return mColumnToKeep;
	}

	public String getLatexColumnTitle() {
		return mLatexTableTitle;
	}

	public ConversionContext getConversionContext() {
		return mConversionContext;
	}

	public Aggregate getSingleRunToOneRow() {
		return mSingleRunToOneRow;
	}

	public Aggregate getManyRunsToOneRow() {
		return mManyRunsToOneRow;
	}
}
