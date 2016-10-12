/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.csv;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Parser for CSV files to Ultimate representation.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class CsvProviderFromFile {
	private static final String COMMA = ",";
//	private final ILogger mLogger;

//	/**
//	 * @param services
//	 *            Ultimate services.
//	 */
//	public CsvProviderFromFile(final IUltimateServiceProvider services) {
//		mLogger = services.getLoggingService().getLogger(this.getClass());
//	}
	
	/**
	 * @param file
	 *            A CSV file.
	 * @return Ultimate representation of a CSV
	 */
	@SuppressWarnings("squid:S2259")
	public static ICsvProvider<String> parse(final File file) {
		ICsvProvider<String> result = null;
		try (BufferedReader reader = new BufferedReader(new FileReader(file))) {
			String line;
			
			// read head row
			if ((line = reader.readLine()) != null) {
				final List<String> columns = split(line);
				result = new SimpleCsvProvider<>(columns);
			}
			
			// read remaining rows
			while ((line = reader.readLine()) != null) {
				result.addRow(split(line));
			}
		} catch (final FileNotFoundException e) {
			e.printStackTrace();
//			if (mLogger.isWarnEnabled()) {
//				mLogger.warn("The CSV file " + file + " does not exist.");
//			}
		} catch (final IOException e) {
//			if (mLogger.isWarnEnabled()) {
//				mLogger.warn("IOException while parsing CSV.");
//			}
		}
		
		return result == null ? new SimpleCsvProvider<>(Collections.emptyList()) : result;
	}
	
	private static List<String> split(final String line) {
		return Arrays.asList(line.split(COMMA));
	}
}
