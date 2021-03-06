/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;


/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Thomas Thuem
 */
public class FMCorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.fm.core";
	
	private static FMCorePlugin plugin;

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.plugin.AbstractUIPlugin#getID()
	 */
	@Override
	public String getID() {
		return PLUGIN_ID;
	}
	


	public static FMCorePlugin getDefault() {
		return plugin;
	}

}
