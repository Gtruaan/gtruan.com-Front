import type { CatRecord } from '../cats';

const ageIntervals = [
    [31536000, 'año', 'años'],
    [2592000, 'mes', 'meses'],
    [86400, 'día', 'días'],
    [3600, 'hora', 'horas'],
    [60, 'minuto', 'minutos'],
    [1, 'segundo', 'segundos'],
] as const;

function calculateAge(creation: CatRecord['creation']) {
    const seconds = (Date.now() - new Date(creation).getTime()) / 1000;

    for (const [duration, singular, plural] of ageIntervals) {
        const count = Math.floor(seconds / duration);

        if (count >= 1) {
            return `${count} ${count === 1 ? singular : plural}`;
        }
    }

    return 'desconocido (scary)';
}

export default function Cat({ cat }: { cat: CatRecord }) {
    return (
        <li className='cat'>
            <img
                className='cat-icon'
                src={`/assets/cat-icons/${encodeURIComponent(cat.variation)}.png`}
                alt=''
                width='180'
                height='180'
            />
            <h3 className='cat-name'>{cat.name}</h3>
            <p>Edad: {calculateAge(cat.creation)}</p>
        </li>
    );
}
