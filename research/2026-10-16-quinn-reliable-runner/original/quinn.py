# Iterates through a CSV file of coordinates and creates a viewshed for each coordinate
# Also creates a weighted copy of each viewshed based on traffic count in the CSV
# Creates compressed versions of both files and deletes the uncompressed versions
# Requires Python, GDAL, and GDAL Python bindings (with all required dependencies)
# This code is distributed under the same license as the article it was shared with
import os
import csv

# Set up required file paths
# These require modification based on Python and QGIS versions
# Output folders must be created manually before running this code
pythonPath = 'c:\\Users\\USERNAME\\AppData\\Local\\Programs\\Python\\Python38\\python.exe'
gdalPath = 'c:\\"Program Files\\QGIS 3.16"\\bin'
gdalPyPath = 'c:\\Program Files\\QGIS 3.16\\apps\\Python37\\Scripts'
dataPath = r'd:\viewshed_analysis'
outputFolder = os.path.join(dataPath, 'outputGdal')
outputFolderWeighted = os.path.join(dataPath, 'outputGdalWeighted')
csvFile = 'points_to_analyze.csv'
demFile = 'clipped_nad83_1arcsec.tif'
csvPath = os.path.join(dataPath, csvFile)
demPath = os.path.join(dataPath, demFile)

# Open the CSV and get the X, Y, ID, and traffic count columns
with open(csvPath, 'r') as pointsCSV:
    csvReader = csv.reader(pointsCSV)
    header = next(csvReader)
    xIndex = header.index('X')
    yIndex = header.index('Y')
    idIndex = header.index('TARGET_FID')
    aadtIndex = header.index('AADT')
    
    itemsProcessed = 0

    for row in csvReader:

        # Read the coordinate
        xCoord = row[xIndex]
        yCoord = row[yIndex]
        id = row[idIndex]
        aadt = row[aadtIndex]
        
        try:

            # Construct output path
            outViewshed = os.path.join(outputFolder, 'vizUncompressed' + id + '.tif')
            outViewshedUInt = os.path.join(outputFolder, 'viz' + id + '.tif')
            outWeightedViewshed = os.path.join(outputFolderWeighted, 'vizaadtUncompressed' + id + '.tif')
            outCompressedWeightedViewshed = os.path.join(outputFolderWeighted, 'vizaadt' + id + '.tif')

            # Construct the viewshed command
            viewshedCmd = gdalPath + r'\gdal_viewshed.exe -ox ' + xCoord + ' -oy ' + yCoord + ' -oz 1 -vv 1 -cc 0.85714 "' + demPath + '" "' + outViewshed + '"'
            os.system(viewshedCmd)
            
            # Convert viewshed type to unsigned integer and compress file
            translateCmd = gdalPath + r'\gdal_translate.exe -ot UInt32  -co COMPRESS=DEFLATE -co PREDICTOR=2 -co ZLEVEL=9 "' + outViewshed + '" "' + outViewshedUInt + '"'
            os.system(translateCmd)
            
            # Delete uncompressed viewshed
            os.remove(outViewshed)
            
            # Weight viewshed by traffic count and save as separate file
            calcCmd = pythonPath + ' ' + '"' + gdalPyPath + '\\gdal_calc.py"' + ' -A "' + outViewshedUInt + r'" --calc="(A)*' + aadt + '" --outfile "' + outWeightedViewshed + '"'
            os.system(calcCmd)
            
            # Compress weighted viewshed
            translateWeightedCmd = gdalPath + r'\gdal_translate.exe -co COMPRESS=DEFLATE -co PREDICTOR=2 -co ZLEVEL=9 "' + outWeightedViewshed + '" "' + outCompressedWeightedViewshed + '"'
            os.system(translateWeightedCmd)
            
            # Delete uncompressed weighted viewshed
            os.remove(outWeightedViewshed)
                 
        except:
            print('Error processing item with ID ' + id)
        
        finally:
            itemsProcessed += 1
            print('Processed ' + str(itemsProcessed) + ' items')
        
        
        


