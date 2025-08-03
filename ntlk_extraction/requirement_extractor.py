import nltk
import re
from nltk.tokenize import sent_tokenize

try:
    nltk.data.find('tokenizers/punkt')
except LookupError:
    nltk.download('punkt')

fr_keywords = ['shall', 'will', 'must', 'should', 'enable', 'allow', 'provide', 'support',
               'facilitate', 'manage', 'process', 'generate', 'send', 'handle', 'create',
               'define', 'receive', 'book', 'schedule', 'monitor', 'track', 'analyze',
               'connect', 'integrate', 'deploy', 'collect', 'alert', 'notify', 'respond',
               'offer', 'ensure', 'improve', 'optimize']

nfr_keywords = ['security', 'privacy', 'compliance', 'encryption', 'authentication',
                'availability', 'reliability', 'scalability', 'performance', 'usability',
                'accessibility', 'fault-tolerant', 'backup', 'redundancy', 'standards',
                'regulatory', 'hipaa', 'gdpr', 'multi-factor', 'role-based', 'encrypted',
                'secure', 'high availability', 'uninterrupted', 'contingency', 'cloud-based']

def extract_requirements(text):
    sentences = sent_tokenize(text)
    fr_sentences = [s.strip() for s in sentences if any(kw in s.lower() for kw in fr_keywords)]
    nfr_sentences = [s.strip() for s in sentences if any(kw in s.lower() for kw in nfr_keywords)]
    return fr_sentences, nfr_sentences

def format_output(fr_sentences, nfr_sentences):
    output = ["Functional Requirements\n"]
    for i, sentence in enumerate(fr_sentences, 1):
        cleaned = re.sub(r'\s+', ' ', sentence.strip())
        if not cleaned.endswith(('.', '!', '?')):
            cleaned += '.'
        if cleaned:
            output.append(f"FR{i}: {cleaned[0].upper() + cleaned[1:]}\n")
    
    output.append("\nNon-Functional Requirements\n")
    for i, sentence in enumerate(nfr_sentences, 1):
        cleaned = re.sub(r'\s+', ' ', sentence.strip())
        if not cleaned.endswith(('.', '!', '?')):
            cleaned += '.'
        if cleaned:
            output.append(f"NFR{i}: {cleaned[0].upper() + cleaned[1:]}\n")
    
    return "".join(output)

def main():
    try:
        with open("resources/system_description.txt", 'r', encoding='utf-8') as file:
            system_description = file.read()
    except FileNotFoundError:
        print("Error: resources/system_description.txt not found!")
        return
    
    fr_sentences, nfr_sentences = extract_requirements(system_description)
    formatted_output = format_output(fr_sentences, nfr_sentences)
    
    with open("ntlk_extracted_requirements.txt", 'w', encoding='utf-8') as file:
        file.write(formatted_output)
    
    print(f"Requirements extracted and saved to ntlk_extracted_requirements.txt")
    print(f"Found {len(fr_sentences)} functional requirements")
    print(f"Found {len(nfr_sentences)} non-functional requirements")

if __name__ == "__main__":
    main() 