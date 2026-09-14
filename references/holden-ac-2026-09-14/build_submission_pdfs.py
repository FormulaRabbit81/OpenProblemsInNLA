from pathlib import Path
from io import BytesIO
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer
from reportlab.lib.styles import getSampleStyleSheet
from pypdf import PdfReader, PdfWriter
import json
base=Path(__file__).resolve().parent
reports={
'AC-01':'AC01_round3_research_pack/report/AC01_round3_report.pdf',
'AC-02':'AC02_updated_research_pack/round2/report/AC02_continuation.pdf',
'AC-03':'AC03_updated_pack/AC03_round3_verified/report.pdf',
'AC-04':'AC04_symmetric_extraction/report.pdf',
'AC-05':'AC05_power_rigidity/report/AC05_power_rigidity.pdf',
'AC-06':'AC06_round4/report.pdf'}
styles=getSampleStyleSheet()
for ident,rel in reports.items():
 text=[ident+' - Research submission', 'Sidney Holden', 'Center for Computational Biology<br/>Flatiron Institute, Simons Foundation', '14 September 2026', 'Partial research; the original problem remains open.', 'Authorship is recorded at the author\'s request. The affiliation was verified against the Simons Foundation staff profile and current CCB directory on 14 September 2026. These sources identify Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks.', 'Affiliation source: <link href="https://www.simonsfoundation.org/people/sidney-holden/" color="blue">Simons Foundation staff profile</link>.', 'The supplied research used substantial AI assistance. Separate Codex AI agents performed informal mathematical reviews for this submission. The linked review records delimit the claims that passed and any missing checks. This is not external human peer review or formal verification. No Lean verification was performed. No first-discovery claim is made; prior-source credit in the report is retained.', 'This cover is followed by the original supplied report, without changes to its pages. Its internal section and page numbers are unchanged. Any original AI byline describes drafting provenance; this cover supplies the requested submission authorship. The accompanying source archive, independent reviews and submission record govern the review scope.', 'See README.md and verification/ in references/holden-ac-2026-09-14 for the exact target comparison and review limitations.']
 (base/(ident+'-cover.json')).write_text(json.dumps(text,indent=2)+'\n')
 mem=BytesIO(); doc=SimpleDocTemplate(mem,pagesize=(612,792),rightMargin=60,leftMargin=60,topMargin=60,bottomMargin=60)
 flow=[]
 for j,s in enumerate(text):
  sty=styles['Title'] if j==0 else styles['Heading2'] if j==1 else styles['BodyText']
  flow.extend([Paragraph(s,sty),Spacer(1,12)])
 doc.build(flow)
 writer=PdfWriter(clone_from=base/'submitted'/rel); writer.insert_page(PdfReader(mem).pages[0],0)
 writer.add_metadata({'/Author':'Sidney Holden','/Title':ident+' - Research submission','/Subject':'Partial research; independent informal AI review; original target remains open'})
 with (base/(ident+'-submission.pdf')).open('wb') as f: writer.write(f)
 print(ident,len(writer.pages))
