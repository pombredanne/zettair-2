import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.StringTokenizer;

public class FixNotParsed {
	public static void main(String[] args) throws IOException
	{
		BufferedReader br1 = new BufferedReader(new FileReader(new File("new_description_not_parsed.txt")));
		BufferedWriter wr1 = new BufferedWriter(new FileWriter(new File("new_description_not_parsed_fixed1.txt")));
		
		String line = br1.readLine(); //doc
		while(line != null)
		{
			wr1.write(line);
			wr1.newLine();
			line = br1.readLine(); //doc no
			wr1.write(line);
			wr1.newLine();
			StringTokenizer tkn = new StringTokenizer(line);
			String id = tkn.nextToken();
			id = tkn.nextToken();
			//String url = tkn.nextToken();
			line = br1.readLine(); //text
			wr1.write(line);
			wr1.newLine();
			line = br1.readLine(); //summary
			wr1.write(line);
			wr1.newLine();
			line = br1.readLine();
			String docend = "";
			int count = 0;
			while(!(docend.equalsIgnoreCase("</DOC>")))
			{
				while(!(line.equalsIgnoreCase("</TEXT>")))
				{
					if((line.indexOf("</TEXT>") == -1) && (line.indexOf("</text>") == -1) && (line.indexOf("<TEXT>") == -1) && (line.indexOf("<text>") == -1) && (line.indexOf("<doc>") == -1) && (line.indexOf("</doc>") == -1) && (line.indexOf("<DOC>") == -1) && (line.indexOf("</DOC>") == -1))
					{
						if(!(id.equalsIgnoreCase("1181606")))
						{
							wr1.write(line);
							wr1.newLine();
						}
						else
						{
							count++;
							System.out.println("gecccc " + count);
						}
					}
					line = br1.readLine();
				}
				docend = br1.readLine();
				line = docend;
			}
			wr1.write("</TEXT>");
			wr1.newLine();
			wr1.write(docend);
			wr1.newLine();
			line = br1.readLine();
		}
		br1.close();
		wr1.close();
	}
}
