const API_URL = 'https://gtruan.pythonanywhere.com/cats';

export type CatRecord = {
    id: number | string;
    name: string;
    creation: string | number;
    variation: string;
};

type NewCat = Pick<CatRecord, 'name' | 'variation'>;

function isCatRecord(value: unknown): value is CatRecord {
    return typeof value === 'object' && value !== null
        && 'id' in value && (typeof value.id === 'number' || typeof value.id === 'string')
        && 'name' in value && typeof value.name === 'string'
        && 'creation' in value && (typeof value.creation === 'string' || typeof value.creation === 'number')
        && 'variation' in value && typeof value.variation === 'string';
}

export async function getCats(signal: AbortSignal): Promise<CatRecord[]> {
    const response = await fetch(API_URL, { signal });

    if (!response.ok) {
        throw new Error(`Cat list request failed (${response.status})`);
    }

    const cats: unknown = await response.json();

    if (!Array.isArray(cats) || !cats.every(isCatRecord)) {
        throw new Error('Invalid cat list response');
    }

    return cats.reverse();
}

export async function createCat(cat: NewCat): Promise<void> {
    const response = await fetch(API_URL, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(cat),
    });

    if (!response.ok) {
        throw new Error(`Cat creation request failed (${response.status})`);
    }
}
